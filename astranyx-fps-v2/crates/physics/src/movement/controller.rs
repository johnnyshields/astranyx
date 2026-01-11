//! Player movement controller.
//!
//! This is the main entry point for player movement. It takes input commands
//! and updates the movement state through the collision world.

use glam::Vec3;

use crate::collision::{CollisionWorld, ContentFlags, TraceShape};

use super::config::MovementConfig;
use super::slide_move::{clip_velocity, step_slide_move};
use super::state::{CommandButtons, MovementFlags, MovementState, PlayerCommand};

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

        // Handle crouching
        self.update_crouch(state, command, world, delta_time);

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

    fn update_crouch(
        &self,
        state: &mut MovementState,
        command: &PlayerCommand,
        world: &CollisionWorld,
        delta_time: f32,
    ) {
        let wants_crouch = command.wants_crouch();
        let is_crouching = state.flags.crouching();

        if wants_crouch && !is_crouching {
            // Start crouching
            state.flags.set(MovementFlags::CROUCHING, true);
        } else if !wants_crouch && is_crouching {
            // Try to stand up - check if there's room
            if self.can_stand_up(state, world) {
                state.flags.set(MovementFlags::CROUCHING, false);
            }
        }

        // Smooth crouch transition
        let target_fraction = if state.flags.crouching() { 1.0 } else { 0.0 };
        let crouch_speed = 1000.0 / self.config.crouch_time_ms as f32;
        let change = crouch_speed * delta_time;

        if state.crouch_fraction < target_fraction {
            state.crouch_fraction = (state.crouch_fraction + change).min(target_fraction);
        } else {
            state.crouch_fraction = (state.crouch_fraction - change).max(target_fraction);
        }
    }

    fn can_stand_up(&self, state: &MovementState, world: &CollisionWorld) -> bool {
        let standing_shape = TraceShape::Capsule {
            radius: self.config.player_radius,
            height: self.config.standing_height,
        };

        !world.point_in_solid(state.position, standing_shape, ContentFlags::MASK_PLAYER_SOLID)
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

        // Determine max speed based on state
        let is_crouching = state.flags.crouching();
        let is_sprinting = command.wants_sprint() && !is_crouching;
        let max_speed = self.config.max_speed(is_crouching, is_sprinting);

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
        let height = self.config.height(state.flags.crouching());
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

        // Start on the ground - position at y=0 which is on top of the floor
        let mut state = MovementState::new(Vec3::new(0.0, 0.0, 0.0));

        // First update to detect ground
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
}
