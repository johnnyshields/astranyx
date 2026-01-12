//! Player movement controller.
//!
//! This is the main entry point for player movement. It takes input commands
//! and updates the movement state through the collision world.

use glam::Vec3;

use crate::collision::{CollisionWorld, ContentFlags, TraceShape};

use super::config::MovementConfig;
use super::slide_move::{clip_velocity, step_slide_move};
use super::stance::{Stance, StanceInput};
use super::state::{MovementFlags, MovementState, PlayerCommand};

/// Player movement controller.
///
/// Handles all player movement physics including:
/// - Ground and air movement
/// - Jumping and crouching
/// - Friction and acceleration
/// - Collision response
///
/// # Example
///
/// ```ignore
/// let mut controller = PlayerController::new(MovementConfig::default());
/// let mut state = MovementState::new(spawn_position);
///
/// // Each frame:
/// controller.update(&mut state, &command, &world, delta_time);
/// ```
#[derive(Debug, Clone)]
pub struct PlayerController {
    /// Movement configuration.
    pub config: MovementConfig,
}

impl PlayerController {
    /// Create a new player controller with the given configuration.
    pub fn new(config: MovementConfig) -> Self {
        Self { config }
    }

    /// Create a controller with default configuration.
    pub fn with_default_config() -> Self {
        Self::new(MovementConfig::default())
    }

    /// Initialize a player's position at spawn.
    ///
    /// This traces down from the spawn point to find the ground and positions
    /// the player correctly above it. Should be called once when spawning.
    pub fn spawn_at(&self, state: &mut MovementState, spawn_pos: Vec3, world: &CollisionWorld) {
        // Start slightly above the spawn point to trace down
        let trace_start = spawn_pos + Vec3::new(0.0, 1.0, 0.0);
        let trace_end = spawn_pos - Vec3::new(0.0, 2.0, 0.0);

        let shape = TraceShape::Capsule {
            radius: self.config.player_radius,
            height: self.config.standing_height,
        };

        let trace = world.trace(trace_start, trace_end, shape, ContentFlags::MASK_PLAYER_SOLID);

        if trace.hit_something() {
            // Position player at the trace end (on top of ground)
            state.position = trace.end_position;
            state.flags.set(MovementFlags::ON_GROUND, true);
            state.ground_entity = 0;
            if let Some(normal) = trace.hit_normal {
                state.ground_normal = normal;
            }
        } else {
            // No ground found, use spawn position as-is
            state.position = spawn_pos;
        }
    }

    /// Update player movement for one frame.
    ///
    /// This is the main entry point that should be called each simulation tick.
    ///
    /// # Arguments
    ///
    /// * `state` - The player's movement state (will be modified)
    /// * `command` - The player's input command for this frame
    /// * `world` - The collision world
    /// * `delta_time` - Time step in seconds
    pub fn update(
        &self,
        state: &mut MovementState,
        command: &PlayerCommand,
        world: &CollisionWorld,
        delta_time: f32,
    ) {
        // Don't move if dead or frozen
        if !state.flags.can_move() {
            return;
        }

        // Clamp delta time to prevent physics explosions
        let delta_time = delta_time.min(0.066); // Max ~66ms (15 FPS minimum)

        // Update view angles
        self.update_view_angles(state, command);

        // Handle stance (crouch/prone)
        self.update_stance(state, command, world, delta_time);

        // Detect ground
        self.check_ground(state, world);

        // Decrement timers
        self.update_timers(state, delta_time);

        // Movement based on current state
        if state.flags.on_ground() {
            self.ground_move(state, command, world, delta_time);
        } else {
            self.air_move(state, command, world, delta_time);
        }

        // Re-check ground after movement
        self.check_ground(state, world);
    }

    // ========================================================================
    // View Angles
    // ========================================================================

    fn update_view_angles(&self, state: &mut MovementState, command: &PlayerCommand) {
        // Apply view angle deltas
        state.view_angles.x += command.view_delta.0; // Pitch
        state.view_angles.y += command.view_delta.1; // Yaw

        // Clamp pitch to prevent looking beyond vertical
        const PITCH_LIMIT: f32 = std::f32::consts::FRAC_PI_2 - 0.01;
        state.view_angles.x = state.view_angles.x.clamp(-PITCH_LIMIT, PITCH_LIMIT);

        // Normalize yaw to -PI..PI
        while state.view_angles.y > std::f32::consts::PI {
            state.view_angles.y -= std::f32::consts::TAU;
        }
        while state.view_angles.y < -std::f32::consts::PI {
            state.view_angles.y += std::f32::consts::TAU;
        }
    }

    // ========================================================================
    // Crouching
    // ========================================================================

    fn update_stance(
        &self,
        state: &mut MovementState,
        command: &PlayerCommand,
        world: &CollisionWorld,
        delta_time: f32,
    ) {
        // Build stance input from command
        let delta_time_ms = (delta_time * 1000.0) as u32;
        let stance_input = StanceInput {
            crouch_pressed: command.wants_crouch(),
            prone_pressed: command.wants_prone(),
            // Jump stands up only if grounded and not jumping
            stand_requested: command.wants_jump() && state.flags.on_ground() && !state.flags.jumping(),
            delta_time_ms,
        };

        // Update stance state machine
        let result = state.stance.update(stance_input);

        // Apply desired stance, with collision checks for going higher
        let mut actual_stance = result.desired_stance;

        // Only check collision if going to a HIGHER stance
        if result.needs_stand_check {
            match result.desired_stance {
                Stance::Standing => {
                    // Want to stand - check if we can
                    let can_stand = self.can_stand_up(state, world);
                    log::debug!(
                        "wants to stand: can_stand={} pos={:?} current={:?}",
                        can_stand, state.position, state.stance.current_stance
                    );
                    if !can_stand {
                        // Can't stand, try crouch
                        if self.can_crouch(state, world) {
                            actual_stance = Stance::Crouching;
                        } else {
                            actual_stance = Stance::Prone;
                        }
                    }
                }
                Stance::Crouching => {
                    // Want to crouch (from prone) - check if we can
                    if !self.can_crouch(state, world) {
                        actual_stance = Stance::Prone;
                    }
                }
                Stance::Prone => {
                    // Already at lowest, no check needed
                }
            }
        } else if result.needs_crouch_check && !self.can_crouch(state, world) {
            // Can't crouch from prone
            actual_stance = Stance::Prone;
        }

        // Apply final stance
        state.stance.apply_stance(actual_stance);

        // Sync flags from stance state
        state.sync_flags_from_stance();

        // Smooth stance transitions using fractions
        //
        // The fractions represent how "lowered" we are:
        // - crouch_fraction: 0 = standing height, 1 = crouching height
        // - prone_fraction: 0 = crouching height, 1 = prone height
        //
        // Key insight: prone is "below" crouch, so when prone, crouch_fraction
        // should be 1.0 to prevent flashing through standing on Prone->Crouch.

        let is_crouching = state.stance.is_crouching();
        let is_prone = state.stance.is_prone();

        // Crouch fraction target:
        // - If prone: force to 1.0 (we're "past" crouch)
        // - If crouching: animate to 1.0
        // - If standing: animate to 0.0
        let crouch_target = if is_prone || is_crouching { 1.0 } else { 0.0 };
        let crouch_speed = 1000.0 / self.config.crouch_time_ms as f32;
        let crouch_change = crouch_speed * delta_time;

        if state.crouch_fraction < crouch_target {
            state.crouch_fraction = (state.crouch_fraction + crouch_change).min(crouch_target);
        } else {
            state.crouch_fraction = (state.crouch_fraction - crouch_change).max(crouch_target);
        }

        // Prone fraction target
        let prone_target = if is_prone { 1.0 } else { 0.0 };
        let prone_speed = 1000.0 / self.config.prone_time_ms as f32;
        let prone_change = prone_speed * delta_time;

        if state.prone_fraction < prone_target {
            state.prone_fraction = (state.prone_fraction + prone_change).min(prone_target);
        } else {
            state.prone_fraction = (state.prone_fraction - prone_change).max(prone_target);
        }
    }

    fn can_stand_up(&self, state: &MovementState, world: &CollisionWorld) -> bool {
        // Check if there's clearance at standing head height
        // Use a sphere the size of the player's radius at the top of the standing capsule
        let head_pos = state.position + Vec3::new(0.0, self.config.standing_height - self.config.player_radius, 0.0);
        let head_shape = TraceShape::Capsule {
            radius: self.config.player_radius,
            height: self.config.player_radius * 2.0,
        };
        !world.point_in_solid(head_pos, head_shape, ContentFlags::MASK_PLAYER_SOLID)
    }

    fn can_crouch(&self, state: &MovementState, world: &CollisionWorld) -> bool {
        // Check if there's clearance at crouching head height
        let head_pos = state.position + Vec3::new(0.0, self.config.crouching_height - self.config.player_radius, 0.0);
        let head_shape = TraceShape::Capsule {
            radius: self.config.player_radius,
            height: self.config.player_radius * 2.0,
        };
        !world.point_in_solid(head_pos, head_shape, ContentFlags::MASK_PLAYER_SOLID)
    }

    // ========================================================================
    // Ground Detection
    // ========================================================================

    fn check_ground(&self, state: &mut MovementState, world: &CollisionWorld) {
        let shape = self.current_shape(state);

        // Trace downward a small amount
        let trace_distance = 0.1; // 10cm
        let trace_end = state.position - Vec3::new(0.0, trace_distance, 0.0);

        let trace = world.trace(
            state.position,
            trace_end,
            shape,
            ContentFlags::MASK_PLAYER_SOLID,
        );

        if trace.hit_something() {
            if let Some(normal) = trace.hit_normal {
                // Check if surface is walkable (not too steep)
                if normal.y >= self.config.min_ground_normal {
                    // Don't detect ground if we're moving upward (just jumped)
                    if state.velocity.y > 0.1 {
                        state.flags.set(MovementFlags::ON_GROUND, false);
                        state.ground_entity = -1;
                        state.ground_normal = Vec3::Y;
                        return;
                    }

                    state.flags.set(MovementFlags::ON_GROUND, true);
                    state.ground_entity = 0; // World
                    state.ground_normal = normal;

                    // Snap to ground if close
                    if trace.fraction < 1.0 {
                        state.position = trace.end_position;
                    }

                    // Clear jumping flag if we've landed
                    if state.timer_ms == 0 {
                        state.flags.set(MovementFlags::JUMPING, false);
                    }

                    return;
                }
            }
        }

        // Not on ground
        state.flags.set(MovementFlags::ON_GROUND, false);
        state.ground_entity = -1;
        state.ground_normal = Vec3::Y;
    }

    // ========================================================================
    // Timers
    // ========================================================================

    fn update_timers(&self, state: &mut MovementState, delta_time: f32) {
        let decrease_ms = (delta_time * 1000.0) as u32;
        state.timer_ms = state.timer_ms.saturating_sub(decrease_ms);
    }

    // ========================================================================
    // Ground Movement
    // ========================================================================

    fn ground_move(
        &self,
        state: &mut MovementState,
        command: &PlayerCommand,
        world: &CollisionWorld,
        delta_time: f32,
    ) {
        // Check for jump
        if command.wants_jump() && !state.flags.jumping() && state.timer_ms == 0 {
            self.do_jump(state);
            self.air_move(state, command, world, delta_time);
            return;
        }

        // Apply friction
        self.apply_friction(state, delta_time);

        // Calculate wish velocity from input
        let (wish_direction, wish_speed) = self.calculate_wish_velocity(state, command);

        // Accelerate
        self.accelerate(
            state,
            wish_direction,
            wish_speed,
            self.config.ground_acceleration,
            delta_time,
        );

        // Clip velocity to ground plane for smooth slope movement
        state.velocity = clip_velocity(state.velocity, state.ground_normal, self.config.overbounce);

        // Don't move if velocity is negligible
        if state.velocity.length_squared() < 0.001 {
            state.velocity = Vec3::ZERO;
            return;
        }

        // Perform movement with step climbing
        let shape = self.current_shape(state);
        step_slide_move(
            world,
            &mut state.position,
            &mut state.velocity,
            shape,
            delta_time,
            &self.config,
            Some(state.ground_normal),
        );
    }

    fn do_jump(&self, state: &mut MovementState) {
        state.velocity.y = self.config.jump_velocity;
        state.flags.set(MovementFlags::ON_GROUND, false);
        state.flags.set(MovementFlags::JUMPING, true);
        state.timer_ms = self.config.jump_cooldown_ms;
        state.ground_entity = -1;
    }

    fn apply_friction(&self, state: &mut MovementState, delta_time: f32) {
        let speed = state.velocity.length();

        if speed < 0.1 {
            // Stop completely when moving very slowly
            state.velocity.x = 0.0;
            state.velocity.z = 0.0;
            return;
        }

        // Calculate friction drop
        let control = speed.max(self.config.stop_speed);
        let drop = control * self.config.friction * delta_time;

        // Apply friction
        let new_speed = (speed - drop).max(0.0);
        if new_speed != speed {
            let factor = new_speed / speed;
            state.velocity *= factor;
        }
    }

    // ========================================================================
    // Air Movement
    // ========================================================================

    fn air_move(
        &self,
        state: &mut MovementState,
        command: &PlayerCommand,
        world: &CollisionWorld,
        delta_time: f32,
    ) {
        // Apply gravity
        state.velocity.y -= self.config.gravity * delta_time;

        // Calculate wish velocity
        let (wish_direction, wish_speed) = self.calculate_wish_velocity(state, command);

        // Air acceleration (very limited)
        self.accelerate(
            state,
            wish_direction,
            wish_speed * self.config.air_control,
            self.config.air_acceleration,
            delta_time,
        );

        // Perform movement (no step climbing in air)
        let shape = self.current_shape(state);
        step_slide_move(
            world,
            &mut state.position,
            &mut state.velocity,
            shape,
            delta_time,
            &self.config,
            None,
        );
    }

    // ========================================================================
    // Shared Movement Helpers
    // ========================================================================

    fn calculate_wish_velocity(
        &self,
        state: &MovementState,
        command: &PlayerCommand,
    ) -> (Vec3, f32) {
        // Get movement vectors from view angles (horizontal only)
        let forward = state.forward_direction();
        let right = state.right_direction();

        // Calculate wish direction from input
        let wish_velocity = forward * command.forward_move + right * command.right_move;

        let speed_squared = wish_velocity.length_squared();
        if speed_squared < 0.0001 {
            return (Vec3::ZERO, 0.0);
        }

        let wish_direction = wish_velocity / speed_squared.sqrt();

        // Determine max speed based on stance
        let is_crouching = state.stance.is_crouching();
        let is_prone = state.stance.is_prone();
        let is_sprinting = command.wants_sprint() && !is_crouching && !is_prone;
        let max_speed = self.config.max_speed(is_crouching, is_sprinting, is_prone);

        // Scale speed by input magnitude (for analog sticks)
        let input_magnitude = command.forward_move.abs().max(command.right_move.abs()).min(1.0);
        let wish_speed = max_speed * input_magnitude;

        (wish_direction, wish_speed)
    }

    fn accelerate(
        &self,
        state: &mut MovementState,
        wish_direction: Vec3,
        wish_speed: f32,
        acceleration: f32,
        delta_time: f32,
    ) {
        if wish_direction.length_squared() < 0.0001 {
            return;
        }

        // Current speed in the wish direction
        let current_speed = state.velocity.dot(wish_direction);

        // How much more speed we need
        let add_speed = wish_speed - current_speed;
        if add_speed <= 0.0 {
            return;
        }

        // Calculate acceleration amount
        let accel_speed = (acceleration * delta_time * wish_speed).min(add_speed);

        // Apply acceleration
        state.velocity += wish_direction * accel_speed;
    }

    // ========================================================================
    // Utility
    // ========================================================================

    fn current_shape(&self, state: &MovementState) -> TraceShape {
        let height = self.config.height(state.stance.is_crouching(), state.stance.is_prone());
        TraceShape::Capsule {
            radius: self.config.player_radius,
            height,
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::state::CommandButtons;

    fn create_test_world() -> CollisionWorld {
        let mut world = CollisionWorld::new();

        // Floor at y=0
        world.add_box(
            Vec3::new(0.0, -0.5, 0.0),
            Vec3::new(100.0, 0.5, 100.0),
            ContentFlags::SOLID,
        );

        world
    }

    #[test]
    fn test_gravity() {
        let world = CollisionWorld::new(); // No floor - free fall
        let controller = PlayerController::with_default_config();

        let mut state = MovementState::new(Vec3::new(0.0, 10.0, 0.0));
        let command = PlayerCommand::default();

        let initial_y = state.position.y;
        controller.update(&mut state, &command, &world, 0.1);

        // Should have fallen due to gravity
        assert!(state.velocity.y < 0.0, "Should be falling");
    }

    #[test]
    fn test_ground_detection() {
        let world = create_test_world();
        let controller = PlayerController::with_default_config();

        let mut state = MovementState::new(Vec3::new(0.0, 0.0, 0.0));
        let command = PlayerCommand::default();

        controller.update(&mut state, &command, &world, 0.016);

        assert!(state.flags.on_ground(), "Should be on ground");
    }

    #[test]
    fn test_forward_movement() {
        let world = create_test_world();
        let controller = PlayerController::with_default_config();

        let mut state = MovementState::new(Vec3::new(0.0, 0.0, 0.0));
        state.flags.set(MovementFlags::ON_GROUND, true);
        state.view_angles.y = 0.0; // Facing +X

        let mut command = PlayerCommand::default();
        command.forward_move = 1.0;

        let start_pos = state.position;

        // Run several frames
        for _ in 0..30 {
            controller.update(&mut state, &command, &world, 0.033);
        }

        // Should have moved forward
        let distance = (state.position - start_pos).length();
        assert!(distance > 1.0, "Should have moved forward, distance={}", distance);
    }

    #[test]
    fn test_jump() {
        let world = create_test_world();
        let controller = PlayerController::with_default_config();

        // Start slightly above the ground - capsule bottom at y=0.1
        // The ground surface is at y=0, so this ensures we're not embedded
        let mut state = MovementState::new(Vec3::new(0.0, 0.1, 0.0));

        // First update to detect ground (will snap to ground)
        let command_idle = PlayerCommand::default();
        controller.update(&mut state, &command_idle, &world, 0.016);
        assert!(state.flags.on_ground(), "Should start on ground");

        // Now jump
        let mut command_jump = PlayerCommand::default();
        command_jump.buttons.press(CommandButtons::JUMP);

        controller.update(&mut state, &command_jump, &world, 0.016);

        // After jumping, we should have upward velocity
        assert!(state.velocity.y > 0.0, "Should have upward velocity, got {}", state.velocity.y);
        assert!(state.flags.jumping(), "Should have jumping flag");
    }

    #[test]
    fn test_crouch() {
        let world = create_test_world();
        let controller = PlayerController::with_default_config();

        let mut state = MovementState::new(Vec3::new(0.0, 0.0, 0.0));
        state.flags.set(MovementFlags::ON_GROUND, true);

        let mut command = PlayerCommand::default();
        command.buttons.press(CommandButtons::CROUCH);

        controller.update(&mut state, &command, &world, 0.016);

        assert!(state.flags.crouching(), "Should be crouching");
    }

    // ========================================================================
    // Spawn Tests
    // ========================================================================

    #[test]
    fn test_spawn_at_finds_ground() {
        let world = create_test_world();
        let controller = PlayerController::with_default_config();

        let mut state = MovementState::default();

        // Spawn at y=0 (exactly on floor surface)
        controller.spawn_at(&mut state, Vec3::new(0.0, 0.0, 0.0), &world);

        // Should be on ground after spawn
        assert!(state.flags.on_ground(), "Should be on ground after spawn");
    }

    #[test]
    fn test_spawn_at_above_ground() {
        let world = create_test_world();
        let controller = PlayerController::with_default_config();

        let mut state = MovementState::default();

        // Spawn at y=0.5 (slightly above floor)
        // spawn_at traces from spawn+1.0 down to spawn-2.0, so this will find the floor
        controller.spawn_at(&mut state, Vec3::new(0.0, 0.5, 0.0), &world);

        // Should trace down and land on ground
        assert!(state.position.y >= 0.0 && state.position.y < 1.0,
            "Should be on ground, got y={}", state.position.y);
        assert!(state.flags.on_ground(), "Should be on ground after spawn");
    }

    #[test]
    fn test_spawn_at_no_ground() {
        let world = CollisionWorld::new(); // Empty world, no floor
        let controller = PlayerController::with_default_config();

        let mut state = MovementState::default();
        let spawn_pos = Vec3::new(0.0, 10.0, 0.0);

        controller.spawn_at(&mut state, spawn_pos, &world);

        // Should use spawn position as-is when no ground found
        assert_eq!(state.position, spawn_pos, "Should use spawn position when no ground");
        assert!(!state.flags.on_ground(), "Should not be on ground");
    }

    #[test]
    fn test_spawn_then_crouch_hold_release_returns_to_standing() {
        // This is the bug that was fixed: initial spawn + hold C + release
        // should return to standing, not go to prone
        let world = create_test_world();
        let controller = PlayerController::with_default_config();

        let mut state = MovementState::default();
        controller.spawn_at(&mut state, Vec3::new(0.0, 0.0, 0.0), &world);

        // Verify initial state
        assert!(state.flags.on_ground(), "Should start on ground");
        assert!(state.stance.is_standing(), "Should start standing");

        // Hold crouch for several frames (> 150ms threshold)
        let mut crouch_cmd = PlayerCommand::default();
        crouch_cmd.buttons.press(CommandButtons::CROUCH);

        for _ in 0..15 {
            controller.update(&mut state, &crouch_cmd, &world, 0.016);
        }

        assert!(state.stance.is_crouching(), "Should be crouching while holding C");

        // Release crouch
        let release_cmd = PlayerCommand::default();
        controller.update(&mut state, &release_cmd, &world, 0.016);

        // Should return to standing (hold behavior), not go to prone
        assert!(state.stance.is_standing(),
            "Should return to standing after releasing held crouch, got {:?}",
            state.stance.current_stance);
    }
}
