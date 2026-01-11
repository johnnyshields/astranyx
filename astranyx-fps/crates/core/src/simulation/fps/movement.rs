//! Player movement for FPS mode.
//!
//! Handles WASD movement, mouse look, and stealth movement modifiers.
//! Generates sound events for footsteps based on movement state.
//! Includes wall collision detection for maze navigation.

use glam::Vec3;

use crate::entities::Player;
use crate::input::PlayerInput;
use crate::level::segment::GeometryDef;
use crate::path::PathSet;
use crate::physics::WorldBounds3D;

use super::collision::{resolve_collisions, PLAYER_HEIGHT, PLAYER_RADIUS};
use super::sound::SoundEvent;
use super::stealth::{Posture, StealthState};
use super::Simulation;

/// Frames between footstep sounds at normal walk speed.
const FOOTSTEP_INTERVAL_WALK: u32 = 20;
/// Frames between footstep sounds when running.
const FOOTSTEP_INTERVAL_RUN: u32 = 10;
/// Frames between footstep sounds when crouching.
const FOOTSTEP_INTERVAL_CROUCH: u32 = 30;

/// Track movement state for footstep timing.
#[derive(Debug, Clone, Default)]
pub struct MovementState {
    /// Frames since last footstep
    pub footstep_timer: u32,
    /// Current stealth state
    pub stealth: StealthState,
}

impl MovementState {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Update player in FPS free movement mode (no collision).
/// Returns any sound events generated (footsteps).
pub fn update_player_fps(
    player: &mut Player,
    input: &PlayerInput,
    bounds: &WorldBounds3D,
) -> Vec<SoundEvent> {
    update_player_fps_with_collision(player, input, bounds, &[])
}

/// Update player in FPS free movement mode with wall collision.
/// Returns any sound events generated (footsteps).
pub fn update_player_fps_with_collision(
    player: &mut Player,
    input: &PlayerInput,
    bounds: &WorldBounds3D,
    geometry: &[GeometryDef],
) -> Vec<SoundEvent> {
    let mut sounds = Vec::new();

    // Mouse look
    let (dx, dy) = input.mouse_delta_radians(0.003);
    player.look_yaw += dx;
    player.look_pitch = (player.look_pitch + dy).clamp(-Player::MAX_PITCH, Player::MAX_PITCH);

    // Determine posture and speed
    let is_crouching = input.focus(); // Repurpose focus as crouch
    let is_running = input.special() && !is_crouching; // Shift to run (special key)

    let posture = if is_crouching {
        Posture::Crouching
    } else {
        Posture::Standing
    };

    // Calculate movement speed
    let base_speed = if is_running {
        Player::FPS_RUN_SPEED
    } else {
        Player::FPS_SPEED
    };
    let speed = base_speed * posture.speed_multiplier();

    // WASD movement relative to look direction (flat, no flying)
    let forward = player.forward_flat();
    let right = player.right_3d();

    let mut move_dir = Vec3::ZERO;
    if input.forward() {
        move_dir += forward;
    }
    if input.backward() {
        move_dir -= forward;
    }
    if input.left() {
        move_dir -= right;
    }
    if input.right() {
        move_dir += right;
    }

    let is_moving = move_dir.length_squared() > 0.0;

    if is_moving {
        player.velocity_3d = move_dir.normalize() * speed;
    } else {
        player.velocity_3d = Vec3::ZERO;
    }

    // Apply movement
    let new_pos = player.position_3d + player.velocity_3d * Simulation::DT;

    // Resolve wall collisions
    let player_height = if is_crouching {
        PLAYER_HEIGHT * 0.6
    } else {
        PLAYER_HEIGHT
    };
    let resolved_pos = resolve_collisions(new_pos, geometry, PLAYER_RADIUS, player_height);
    player.position_3d = resolved_pos;

    // Adjust height based on posture
    let target_y = bounds.min.y + posture.height();
    player.position_3d.y = target_y;

    // Clamp to bounds
    player.position_3d.x = player.position_3d.x.clamp(bounds.min.x, bounds.max.x);
    player.position_3d.z = player.position_3d.z.clamp(bounds.min.z, bounds.max.z);

    player.sync_3d_to_2d();

    // Generate footstep sounds if moving
    if is_moving {
        let interval = if is_crouching {
            FOOTSTEP_INTERVAL_CROUCH
        } else if is_running {
            FOOTSTEP_INTERVAL_RUN
        } else {
            FOOTSTEP_INTERVAL_WALK
        };

        // TODO: Track footstep timer per-player
        // For now, generate footsteps based on frame count
        // This is a simplification - proper implementation would track state
        let should_footstep = (player.fire_cooldown as u32 % interval) == 0;

        if should_footstep {
            sounds.push(SoundEvent::footstep(
                player.position_3d,
                player.id,
                is_running,
                is_crouching,
            ));
        }
    }

    sounds
}

/// Update player in turret/on-rails mode.
/// Position follows a path, player only aims.
pub fn update_player_turret(
    player: &mut Player,
    input: &PlayerInput,
    path_id: &str,
    paths: &PathSet,
    frame: u32,
) {
    if let Some(path) = paths.get(path_id) {
        // Position locked to path
        let (path_pos, _path_rot) = path.sample_at_frame(frame);
        player.position_3d = path_pos + Vec3::new(0.0, 1.7, 0.0); // Eye height
    }

    // Mouse aiming
    let (dx, dy) = input.mouse_delta_radians(0.003);
    player.look_yaw += dx;
    player.look_pitch = (player.look_pitch + dy).clamp(-Player::MAX_PITCH, Player::MAX_PITCH);

    player.sync_3d_to_2d();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::entities::EntityId;
    use glam::Vec2;

    #[test]
    fn test_fps_movement() {
        let mut player = Player::new(EntityId(1), Vec2::ZERO);
        player.position_3d = Vec3::new(100.0, 5.0, 100.0);

        let bounds = WorldBounds3D::new(0.0, 0.0, 0.0, 500.0, 100.0, 500.0);

        // Move forward
        let input = PlayerInput::from_bits(PlayerInput::FORWARD);
        let _sounds = update_player_fps(&mut player, &input, &bounds);

        // Should have moved in the forward direction
        // (initial yaw is 0, so forward is +Z)
        assert!(player.position_3d.z > 100.0 || player.position_3d.x > 100.0);
    }

    #[test]
    fn test_crouch_speed() {
        let mut player = Player::new(EntityId(1), Vec2::ZERO);
        player.position_3d = Vec3::new(100.0, 5.0, 100.0);
        player.look_yaw = 0.0;

        let bounds = WorldBounds3D::new(0.0, 0.0, 0.0, 500.0, 100.0, 500.0);

        // Normal forward movement
        let normal_input = PlayerInput::from_bits(PlayerInput::FORWARD);
        update_player_fps(&mut player, &normal_input, &bounds);
        let normal_vel = player.velocity_3d.length();

        // Reset
        player.position_3d = Vec3::new(100.0, 5.0, 100.0);

        // Crouching forward movement (FOCUS = crouch)
        let crouch_input = PlayerInput::from_bits(PlayerInput::FORWARD | PlayerInput::FOCUS);
        update_player_fps(&mut player, &crouch_input, &bounds);
        let crouch_vel = player.velocity_3d.length();

        assert!(crouch_vel < normal_vel);
    }
}
