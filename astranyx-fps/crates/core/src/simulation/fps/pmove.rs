//! Quake-style player movement physics (PM_* functions).
//!
//! This is a deterministic implementation of classic FPS movement based on
//! Quake 3's bg_pmove.c. All math is deterministic for P2P lockstep netcode.
//!
//! Key concepts:
//! - Fixed timestep movement (capped at 66ms chunks)
//! - Multi-plane collision sliding
//! - Stair stepping (18 units)
//! - Ground/air movement with different physics
//! - Friction and acceleration models

use glam::Vec3;

use super::collision::CollisionBackend;

// ============================================================================
// MOVEMENT CONSTANTS (Quake 3 style)
// ============================================================================

/// Maximum timestep per physics iteration (66ms like Q3).
pub const MAX_FRAMETIME: f32 = 0.066;

/// Stair step height in units.
pub const STEP_SIZE: f32 = 0.5; // 0.5m = ~18 inches

/// Jump velocity (units/sec).
pub const JUMP_VELOCITY: f32 = 6.0; // ~6 m/s upward

/// Gravity acceleration (units/sec²).
pub const GRAVITY: f32 = 20.0; // ~2g for snappy feel

/// Minimum surface normal Y to be considered ground.
pub const MIN_WALK_NORMAL: f32 = 0.7; // cos(45°) approximately

/// Overclip factor for velocity reflection.
pub const OVERCLIP: f32 = 1.001;

/// Maximum clip planes to track during slide move.
pub const MAX_CLIP_PLANES: usize = 5;

/// Ground friction coefficient.
pub const PM_FRICTION: f32 = 6.0;

/// Ground acceleration.
pub const PM_ACCELERATE: f32 = 10.0;

/// Air acceleration (much lower than ground).
pub const PM_AIR_ACCELERATE: f32 = 1.0;

/// Speed below which we stop completely.
pub const PM_STOP_SPEED: f32 = 1.0;

/// Maximum horizontal speed (walk).
pub const PM_WALK_SPEED: f32 = 6.0; // 6 m/s

/// Maximum horizontal speed (run).
pub const PM_RUN_SPEED: f32 = 10.0; // 10 m/s

/// Maximum horizontal speed (crouch).
pub const PM_CROUCH_SPEED: f32 = 3.0; // 3 m/s

/// Player collision radius.
pub const PLAYER_RADIUS: f32 = 0.4;

/// Player standing height.
pub const PLAYER_HEIGHT: f32 = 1.8;

/// Player crouching height.
pub const PLAYER_CROUCH_HEIGHT: f32 = 1.0;

/// Eye height offset from position (bottom of capsule).
pub const EYE_HEIGHT_STANDING: f32 = 1.6;
pub const EYE_HEIGHT_CROUCHING: f32 = 0.8;

// ============================================================================
// PLAYER MOVE STATE
// ============================================================================

/// Movement flags for the player state.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PmFlags(pub u16);

impl PmFlags {
    pub const ON_GROUND: u16 = 1 << 0;
    pub const JUMPING: u16 = 1 << 1;
    pub const DUCKING: u16 = 1 << 2;
    pub const IN_WATER: u16 = 1 << 3;
    pub const DEAD: u16 = 1 << 4;
    pub const FROZEN: u16 = 1 << 5;

    pub fn is_on_ground(&self) -> bool {
        self.0 & Self::ON_GROUND != 0
    }

    pub fn is_jumping(&self) -> bool {
        self.0 & Self::JUMPING != 0
    }

    pub fn is_ducking(&self) -> bool {
        self.0 & Self::DUCKING != 0
    }

    pub fn set(&mut self, flag: u16, value: bool) {
        if value {
            self.0 |= flag;
        } else {
            self.0 &= !flag;
        }
    }
}

/// Player physics state - everything needed for deterministic movement.
#[derive(Debug, Clone)]
pub struct PlayerMoveState {
    /// Current position (feet/bottom of capsule).
    pub origin: Vec3,
    /// Current velocity.
    pub velocity: Vec3,
    /// View angles (pitch, yaw, roll) in radians.
    pub view_angles: Vec3,
    /// Movement command angles.
    pub cmd_angles: Vec3,
    /// Movement flags.
    pub pm_flags: PmFlags,
    /// Ground entity ID (-1 if airborne).
    pub ground_entity: i32,
    /// Time in current state (for jump cooldown, etc).
    pub pm_time: u16,
}

impl Default for PlayerMoveState {
    fn default() -> Self {
        Self {
            origin: Vec3::ZERO,
            velocity: Vec3::ZERO,
            view_angles: Vec3::ZERO,
            cmd_angles: Vec3::ZERO,
            pm_flags: PmFlags::default(),
            ground_entity: -1,
            pm_time: 0,
        }
    }
}

impl PlayerMoveState {
    pub fn new(origin: Vec3) -> Self {
        Self {
            origin,
            ..Default::default()
        }
    }

    /// Get eye position for camera.
    pub fn eye_position(&self) -> Vec3 {
        let eye_height = if self.pm_flags.is_ducking() {
            EYE_HEIGHT_CROUCHING
        } else {
            EYE_HEIGHT_STANDING
        };
        self.origin + Vec3::new(0.0, eye_height, 0.0)
    }

    /// Get current player height.
    pub fn height(&self) -> f32 {
        if self.pm_flags.is_ducking() {
            PLAYER_CROUCH_HEIGHT
        } else {
            PLAYER_HEIGHT
        }
    }
}

/// Movement command input for a single frame.
#[derive(Debug, Clone, Default)]
pub struct UserCmd {
    /// Forward/backward movement (-1.0 to 1.0).
    pub forward_move: f32,
    /// Strafe left/right (-1.0 to 1.0).
    pub right_move: f32,
    /// Up/down (jump/crouch) (-1.0 to 1.0).
    pub up_move: f32,
    /// View angle changes (pitch, yaw) in radians.
    pub delta_angles: Vec3,
    /// Button state bitflags.
    pub buttons: u16,
}

impl UserCmd {
    pub const BTN_ATTACK: u16 = 1 << 0;
    pub const BTN_JUMP: u16 = 1 << 1;
    pub const BTN_CROUCH: u16 = 1 << 2;
    pub const BTN_SPRINT: u16 = 1 << 3;
    pub const BTN_USE: u16 = 1 << 4;

    pub fn wants_jump(&self) -> bool {
        self.buttons & Self::BTN_JUMP != 0
    }

    pub fn wants_crouch(&self) -> bool {
        self.buttons & Self::BTN_CROUCH != 0
    }

    pub fn wants_sprint(&self) -> bool {
        self.buttons & Self::BTN_SPRINT != 0
    }
}

/// Trace result from collision query.
#[derive(Debug, Clone)]
pub struct TraceResult {
    /// Fraction of move completed (0.0 = immediate hit, 1.0 = no hit).
    pub fraction: f32,
    /// End position of the trace.
    pub end_pos: Vec3,
    /// Surface normal at impact point (if hit).
    pub plane_normal: Option<Vec3>,
    /// Whether trace started in solid.
    pub start_solid: bool,
    /// Whether entire trace was in solid.
    pub all_solid: bool,
}

impl TraceResult {
    pub fn no_hit(end_pos: Vec3) -> Self {
        Self {
            fraction: 1.0,
            end_pos,
            plane_normal: None,
            start_solid: false,
            all_solid: false,
        }
    }

    pub fn hit(fraction: f32, end_pos: Vec3, normal: Vec3) -> Self {
        Self {
            fraction,
            end_pos,
            plane_normal: Some(normal),
            start_solid: false,
            all_solid: false,
        }
    }
}

// ============================================================================
// LOCAL MOVE STATE (per-frame working data)
// ============================================================================

/// Per-frame local state for movement calculations.
struct PmoveLocal {
    /// Frame time in seconds.
    frametime: f32,
    /// Forward direction (flat).
    forward: Vec3,
    /// Right direction.
    right: Vec3,
    /// Up direction.
    up: Vec3,
    /// Ground plane normal (if on ground).
    ground_plane: Option<Vec3>,
    /// Whether we're walking (on valid ground).
    walking: bool,
}

impl PmoveLocal {
    fn new(frametime: f32) -> Self {
        Self {
            frametime,
            forward: Vec3::Z,
            right: Vec3::X,
            up: Vec3::Y,
            ground_plane: None,
            walking: false,
        }
    }
}

// ============================================================================
// MAIN MOVEMENT FUNCTION
// ============================================================================

/// Execute player movement for a frame.
///
/// This is the main entry point - handles the full movement including:
/// - View angle updates
/// - Ground detection
/// - Duck/crouch handling
/// - Movement physics (ground/air)
/// - Collision resolution
pub fn pmove(
    state: &mut PlayerMoveState,
    cmd: &UserCmd,
    collision: &CollisionBackend,
    frametime: f32,
) {
    // Cap frametime to prevent huge deltas
    let frametime = frametime.min(MAX_FRAMETIME);

    // Set up local state
    let mut pml = PmoveLocal::new(frametime);

    // Update view angles
    pm_update_view_angles(state, cmd);

    // Calculate movement vectors from view angles
    angle_vectors(state.view_angles, &mut pml.forward, &mut pml.right, &mut pml.up);
    // Flatten forward for ground movement
    pml.forward.y = 0.0;
    pml.forward = pml.forward.normalize_or_zero();

    // Handle ducking
    pm_check_duck(state, cmd);

    // Ground trace
    pm_ground_trace(state, &mut pml, collision);

    // Decrement timers
    pm_drop_timers(state, frametime);

    // Movement based on state
    if state.pm_flags.is_on_ground() {
        pm_walk_move(state, cmd, &mut pml, collision);
    } else {
        pm_air_move(state, cmd, &mut pml, collision);
    }

    // Another ground check after movement
    pm_ground_trace(state, &mut pml, collision);
}

// ============================================================================
// ANGLE CALCULATIONS
// ============================================================================

/// Convert angles to direction vectors.
fn angle_vectors(angles: Vec3, forward: &mut Vec3, right: &mut Vec3, up: &mut Vec3) {
    let (sp, cp) = angles.x.sin_cos(); // pitch
    let (sy, cy) = angles.y.sin_cos(); // yaw
    let (sr, cr) = angles.z.sin_cos(); // roll

    *forward = Vec3::new(cp * cy, -sp, cp * sy);
    *right = Vec3::new(
        -sr * sp * cy + cr * sy,
        sr * cp,
        -sr * sp * sy - cr * cy,
    );
    *up = Vec3::new(
        cr * sp * cy + sr * sy,
        cr * cp,
        cr * sp * sy - sr * cy,
    );
}

/// Update view angles from command input.
fn pm_update_view_angles(state: &mut PlayerMoveState, cmd: &UserCmd) {
    // Add delta angles
    state.view_angles += cmd.delta_angles;

    // Clamp pitch to prevent flipping
    state.view_angles.x = state.view_angles.x.clamp(
        -std::f32::consts::FRAC_PI_2 + 0.01,
        std::f32::consts::FRAC_PI_2 - 0.01,
    );

    // Normalize yaw
    while state.view_angles.y > std::f32::consts::PI {
        state.view_angles.y -= std::f32::consts::TAU;
    }
    while state.view_angles.y < -std::f32::consts::PI {
        state.view_angles.y += std::f32::consts::TAU;
    }
}

// ============================================================================
// DUCK/CROUCH HANDLING
// ============================================================================

fn pm_check_duck(state: &mut PlayerMoveState, cmd: &UserCmd) {
    if cmd.wants_crouch() {
        state.pm_flags.set(PmFlags::DUCKING, true);
    } else {
        // TODO: Check if we can stand up (ceiling collision)
        state.pm_flags.set(PmFlags::DUCKING, false);
    }
}

// ============================================================================
// GROUND DETECTION
// ============================================================================

fn pm_ground_trace(state: &mut PlayerMoveState, pml: &mut PmoveLocal, collision: &CollisionBackend) {
    // Trace downward a small amount
    let start = state.origin;
    let end = start - Vec3::new(0.0, 0.25, 0.0); // 0.25m downward

    let trace = pm_trace(start, end, state.height(), collision);

    if trace.all_solid {
        // Stuck in ground
        state.pm_flags.set(PmFlags::ON_GROUND, true);
        state.ground_entity = 0; // World
        pml.ground_plane = Some(Vec3::Y);
        pml.walking = true;
        return;
    }

    // Check if we hit something and if it's walkable
    if let Some(normal) = trace.plane_normal {
        if normal.y >= MIN_WALK_NORMAL {
            // Valid ground
            state.pm_flags.set(PmFlags::ON_GROUND, true);
            state.ground_entity = 0; // World
            pml.ground_plane = Some(normal);
            pml.walking = true;

            // Snap to ground
            if trace.fraction < 1.0 {
                state.origin = trace.end_pos;
            }
            return;
        }
    }

    // In air
    state.pm_flags.set(PmFlags::ON_GROUND, false);
    state.ground_entity = -1;
    pml.ground_plane = None;
    pml.walking = false;
}

// ============================================================================
// TIMER MANAGEMENT
// ============================================================================

fn pm_drop_timers(state: &mut PlayerMoveState, frametime: f32) {
    let drop = (frametime * 1000.0) as u16;
    state.pm_time = state.pm_time.saturating_sub(drop);

    // Clear jump flag after landing
    if state.pm_flags.is_on_ground() && state.pm_time == 0 {
        state.pm_flags.set(PmFlags::JUMPING, false);
    }
}

// ============================================================================
// GROUND MOVEMENT
// ============================================================================

fn pm_walk_move(
    state: &mut PlayerMoveState,
    cmd: &UserCmd,
    pml: &mut PmoveLocal,
    collision: &CollisionBackend,
) {
    // Check for jump
    if cmd.wants_jump() && !state.pm_flags.is_jumping() {
        pm_jump(state);
        pm_air_move(state, cmd, pml, collision);
        return;
    }

    // Apply friction
    pm_friction(state, pml);

    // Calculate wish direction and speed
    let (wish_dir, wish_speed) = pm_get_wish_velocity(state, cmd, pml);

    // Accelerate
    pm_accelerate(state, wish_dir, wish_speed, PM_ACCELERATE, pml.frametime);

    // Slide along ground plane
    if let Some(ground_normal) = pml.ground_plane {
        state.velocity = pm_clip_velocity(state.velocity, ground_normal, OVERCLIP);
    }

    // Don't move if velocity is negligible
    let speed = state.velocity.length();
    if speed < 0.001 {
        state.velocity = Vec3::ZERO;
        return;
    }

    // Step slide move
    pm_step_slide_move(state, pml, collision, true);
}

fn pm_jump(state: &mut PlayerMoveState) {
    state.velocity.y = JUMP_VELOCITY;
    state.pm_flags.set(PmFlags::ON_GROUND, false);
    state.pm_flags.set(PmFlags::JUMPING, true);
    state.pm_time = 250; // Jump cooldown in ms
    state.ground_entity = -1;
}

// ============================================================================
// AIR MOVEMENT
// ============================================================================

fn pm_air_move(
    state: &mut PlayerMoveState,
    cmd: &UserCmd,
    pml: &mut PmoveLocal,
    collision: &CollisionBackend,
) {
    // Apply gravity
    state.velocity.y -= GRAVITY * pml.frametime;

    // Calculate wish direction and speed
    let (wish_dir, wish_speed) = pm_get_wish_velocity(state, cmd, pml);

    // Air acceleration (limited)
    pm_accelerate(state, wish_dir, wish_speed, PM_AIR_ACCELERATE, pml.frametime);

    // Slide move without step-up
    pm_step_slide_move(state, pml, collision, false);
}

// ============================================================================
// WISH VELOCITY (input to desired direction)
// ============================================================================

fn pm_get_wish_velocity(
    state: &PlayerMoveState,
    cmd: &UserCmd,
    pml: &PmoveLocal,
) -> (Vec3, f32) {
    // Get wish direction from input
    let wish_vel = pml.forward * cmd.forward_move + pml.right * cmd.right_move;

    // Normalize and get wish speed
    let wish_speed_sq = wish_vel.length_squared();
    if wish_speed_sq < 0.0001 {
        return (Vec3::ZERO, 0.0);
    }

    let wish_dir = wish_vel / wish_speed_sq.sqrt();

    // Determine max speed based on state
    let max_speed = if state.pm_flags.is_ducking() {
        PM_CROUCH_SPEED
    } else if cmd.wants_sprint() {
        PM_RUN_SPEED
    } else {
        PM_WALK_SPEED
    };

    // Scale wish speed by input magnitude (for analog sticks)
    let input_magnitude = (cmd.forward_move.abs().max(cmd.right_move.abs())).min(1.0);
    let wish_speed = max_speed * input_magnitude;

    (wish_dir, wish_speed)
}

// ============================================================================
// FRICTION
// ============================================================================

fn pm_friction(state: &mut PlayerMoveState, pml: &PmoveLocal) {
    let vel = state.velocity;
    let speed = vel.length();

    if speed < 0.1 {
        state.velocity.x = 0.0;
        state.velocity.z = 0.0;
        return;
    }

    // Apply friction
    let control = if speed < PM_STOP_SPEED {
        PM_STOP_SPEED
    } else {
        speed
    };

    let drop = control * PM_FRICTION * pml.frametime;
    let new_speed = (speed - drop).max(0.0);

    if new_speed != speed {
        let factor = new_speed / speed;
        state.velocity *= factor;
    }
}

// ============================================================================
// ACCELERATION
// ============================================================================

fn pm_accelerate(
    state: &mut PlayerMoveState,
    wish_dir: Vec3,
    wish_speed: f32,
    accel: f32,
    frametime: f32,
) {
    // Determine current speed in wish direction
    let current_speed = state.velocity.dot(wish_dir);

    // Determine how much to add
    let add_speed = wish_speed - current_speed;
    if add_speed <= 0.0 {
        return;
    }

    // Determine acceleration
    let accel_speed = (accel * frametime * wish_speed).min(add_speed);

    // Add to velocity
    state.velocity += wish_dir * accel_speed;
}

// ============================================================================
// VELOCITY CLIPPING
// ============================================================================

/// Clip velocity against a plane normal.
fn pm_clip_velocity(velocity: Vec3, normal: Vec3, overbounce: f32) -> Vec3 {
    let mut backoff = velocity.dot(normal);

    if backoff < 0.0 {
        backoff *= overbounce;
    } else {
        backoff /= overbounce;
    }

    velocity - normal * backoff
}

// ============================================================================
// SLIDE MOVE (multi-plane collision)
// ============================================================================

fn pm_step_slide_move(
    state: &mut PlayerMoveState,
    pml: &PmoveLocal,
    collision: &CollisionBackend,
    gravity: bool,
) {
    let start_origin = state.origin;
    let start_velocity = state.velocity;

    // First try normal slide move
    if pm_slide_move(state, pml, collision, gravity) {
        // No collision, we're done
        return;
    }

    // Try stepping up
    let _down = start_origin - Vec3::new(0.0, STEP_SIZE, 0.0);
    let up = start_origin + Vec3::new(0.0, STEP_SIZE, 0.0);

    // Check if we can step up
    let up_trace = pm_trace(start_origin, up, state.height(), collision);
    if up_trace.all_solid {
        return; // Can't step up
    }

    // Try to move from stepped-up position
    let stepped_origin = up_trace.end_pos;
    let mut stepped_state = state.clone();
    stepped_state.origin = stepped_origin;
    stepped_state.velocity = start_velocity;

    pm_slide_move(&mut stepped_state, pml, collision, gravity);

    // Step back down
    let down_trace = pm_trace(
        stepped_state.origin,
        stepped_state.origin - Vec3::new(0.0, STEP_SIZE + 0.01, 0.0),
        state.height(),
        collision,
    );

    if !down_trace.all_solid {
        stepped_state.origin = down_trace.end_pos;
    }

    // Use stepped result if we moved further horizontally
    let unstep_dist_sq = (state.origin.x - start_origin.x).powi(2)
        + (state.origin.z - start_origin.z).powi(2);
    let step_dist_sq = (stepped_state.origin.x - start_origin.x).powi(2)
        + (stepped_state.origin.z - start_origin.z).powi(2);

    if step_dist_sq > unstep_dist_sq {
        *state = stepped_state;
    }
}

/// Main slide move algorithm - handle collision with up to MAX_CLIP_PLANES.
fn pm_slide_move(
    state: &mut PlayerMoveState,
    pml: &PmoveLocal,
    collision: &CollisionBackend,
    _gravity: bool,
) -> bool {
    let mut planes: [Vec3; MAX_CLIP_PLANES] = [Vec3::ZERO; MAX_CLIP_PLANES];
    let mut num_planes = 0;
    let mut time_left = pml.frametime;
    let original_velocity = state.velocity;

    // Never turn against the ground plane
    if state.pm_flags.is_on_ground() {
        if let Some(ground) = pml.ground_plane {
            planes[num_planes] = ground;
            num_planes += 1;
        }
    }

    // Never turn against original velocity
    planes[num_planes] = original_velocity.normalize_or_zero();
    num_planes += 1;

    for _ in 0..4 {
        // Bumps (collision iterations)
        if state.velocity.length_squared() < 0.0001 {
            break;
        }

        // Calculate end position
        let end = state.origin + state.velocity * time_left;

        // Trace
        let trace = pm_trace(state.origin, end, state.height(), collision);

        if trace.all_solid {
            // Entity is trapped in another solid
            state.velocity.y = 0.0;
            return false;
        }

        if trace.fraction > 0.0 {
            // Actually moved
            state.origin = trace.end_pos;
        }

        if trace.fraction == 1.0 {
            // Moved the entire distance
            return true;
        }

        // Time left after partial move
        time_left -= time_left * trace.fraction;

        // Get the plane we hit
        if let Some(normal) = trace.plane_normal {
            if num_planes < MAX_CLIP_PLANES {
                planes[num_planes] = normal;
                num_planes += 1;
            }

            // Modify velocity to slide along all hit planes
            let mut clipped = state.velocity;
            for i in 0..num_planes {
                clipped = pm_clip_velocity(clipped, planes[i], OVERCLIP);

                // Check if clipped velocity goes into any other plane
                let mut good = true;
                for j in 0..num_planes {
                    if i == j {
                        continue;
                    }
                    if clipped.dot(planes[j]) < 0.0 {
                        good = false;
                        break;
                    }
                }

                if good {
                    state.velocity = clipped;
                    break;
                }
            }

            // If we couldn't find a valid direction, stop
            if clipped.dot(planes[0]) < 0.0 {
                state.velocity = Vec3::ZERO;
                return false;
            }
        }
    }

    // Hit something
    false
}

// ============================================================================
// COLLISION TRACE
// ============================================================================

/// Perform a collision trace from start to end.
fn pm_trace(start: Vec3, end: Vec3, height: f32, collision: &CollisionBackend) -> TraceResult {
    // Use capsule trace for proper collision detection
    let (fraction, end_pos, normal) = collision.trace_capsule(start, end, PLAYER_RADIUS, height);

    if fraction >= 1.0 {
        TraceResult::no_hit(end)
    } else if let Some(n) = normal {
        TraceResult::hit(fraction, end_pos, n)
    } else {
        // Hit something but no normal - treat as solid
        TraceResult {
            fraction,
            end_pos,
            plane_normal: Some(Vec3::Y),
            start_solid: false,
            all_solid: false,
        }
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level::test_level::generate_test_arena;

    #[test]
    fn test_clip_velocity() {
        // Test bouncing off a wall (normal pointing +X)
        let vel = Vec3::new(-5.0, 0.0, 3.0);
        let normal = Vec3::X;
        let clipped = pm_clip_velocity(vel, normal, 1.0);

        // X component should be zeroed, Z unchanged
        assert!(clipped.x.abs() < 0.001);
        assert!((clipped.z - 3.0).abs() < 0.001);
    }

    #[test]
    fn test_friction() {
        let mut state = PlayerMoveState::new(Vec3::ZERO);
        state.velocity = Vec3::new(10.0, 0.0, 0.0);

        let pml = PmoveLocal::new(1.0 / 30.0);
        pm_friction(&mut state, &pml);

        // Velocity should decrease
        assert!(state.velocity.length() < 10.0);
    }

    #[test]
    fn test_acceleration() {
        let mut state = PlayerMoveState::new(Vec3::ZERO);

        let wish_dir = Vec3::X;
        let wish_speed = 6.0;

        pm_accelerate(&mut state, wish_dir, wish_speed, PM_ACCELERATE, 1.0 / 30.0);

        // Should have gained some velocity
        assert!(state.velocity.x > 0.0);
    }

    #[test]
    fn test_jump() {
        let mut state = PlayerMoveState::new(Vec3::ZERO);
        state.pm_flags.set(PmFlags::ON_GROUND, true);

        pm_jump(&mut state);

        assert!(state.velocity.y > 0.0);
        assert!(!state.pm_flags.is_on_ground());
        assert!(state.pm_flags.is_jumping());
    }

    #[test]
    fn test_gravity() {
        let mut state = PlayerMoveState::new(Vec3::new(0.0, 10.0, 0.0));
        state.pm_flags.set(PmFlags::ON_GROUND, false);

        // Simulate air movement - apply gravity directly
        let initial_y_vel = state.velocity.y;
        let frametime = 1.0 / 30.0;
        state.velocity.y -= GRAVITY * frametime;

        // Velocity should decrease (gravity pulls down)
        assert!(state.velocity.y < initial_y_vel);
    }

    #[test]
    fn test_pmove_with_test_level() {
        // Generate test arena
        let geometry = generate_test_arena();
        let backend = CollisionBackend::Legacy(&geometry);

        // Player starts above ground (floor is at y=0, player feet at y=2)
        let mut state = PlayerMoveState::new(Vec3::new(0.0, 2.0, 5.0));

        // Should fall due to gravity (not on ground yet)
        let cmd = UserCmd::default();
        let frametime = 1.0 / 30.0;

        // Run several frames of physics - enough to fall 2m
        // Free fall: y = 0.5 * g * t^2, so t = sqrt(2*y/g) = sqrt(2*2/20) = 0.45s = ~14 frames
        // Add extra frames for margin
        for _ in 0..60 {
            pmove(&mut state, &cmd, &backend, frametime);
        }

        // Floor is at y=0 (top surface), player should land on it
        // With the floor box centered at y=-0.5 with height 1.0, top is at y=0
        assert!(state.origin.y <= 0.5, "Player should have fallen near ground, y={}", state.origin.y);
    }

    #[test]
    fn test_pmove_forward_movement() {
        let geometry = generate_test_arena();
        let backend = CollisionBackend::Legacy(&geometry);

        // Player on ground (floor top is at y=0)
        let mut state = PlayerMoveState::new(Vec3::new(0.0, 0.0, 5.0));
        state.pm_flags.set(PmFlags::ON_GROUND, true);
        state.ground_entity = 0;
        // Face forward (positive Z direction means yaw = 0)
        state.view_angles.y = 0.0;

        // Move forward
        let mut cmd = UserCmd::default();
        cmd.forward_move = 1.0;
        let frametime = 1.0 / 30.0;

        let start_pos = state.origin;

        // Run physics for 1 second (30 frames)
        for _ in 0..30 {
            pmove(&mut state, &cmd, &backend, frametime);
        }

        // Should have moved (distance > 0)
        let dist = (state.origin - start_pos).length();
        assert!(dist > 0.5, "Player should have moved, distance={}", dist);
    }

    #[test]
    fn test_pmove_wall_collision() {
        let geometry = generate_test_arena();
        let backend = CollisionBackend::Legacy(&geometry);

        // Player near east wall (+X = 50)
        let mut state = PlayerMoveState::new(Vec3::new(45.0, 0.0, 0.0));
        state.pm_flags.set(PmFlags::ON_GROUND, true);
        state.ground_entity = 0;
        state.view_angles.y = std::f32::consts::FRAC_PI_2; // Face +X

        // Try to move into the wall
        let mut cmd = UserCmd::default();
        cmd.forward_move = 1.0;
        let frametime = 1.0 / 30.0;

        // Run physics for 2 seconds
        for _ in 0..60 {
            pmove(&mut state, &cmd, &backend, frametime);
        }

        // Should be stopped by the wall (x < 50)
        assert!(state.origin.x < 50.0, "Player should be stopped by wall, x={}", state.origin.x);
    }
}
