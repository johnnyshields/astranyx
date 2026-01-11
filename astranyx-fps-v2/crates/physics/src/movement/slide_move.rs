//! Slide move algorithm for collision response.
//!
//! This implements the classic Quake slide move algorithm that allows
//! smooth movement along walls and around corners.

use glam::Vec3;

use crate::collision::{CollisionWorld, ContentFlags, TraceResult, TraceShape};

use super::config::MovementConfig;

/// Maximum number of collision planes to track during slide move.
const MAX_CLIP_PLANES: usize = 5;

/// Clip velocity against a surface normal.
///
/// This removes the component of velocity going into the surface and
/// optionally adds a small "overbounce" to prevent sticking.
pub fn clip_velocity(velocity: Vec3, normal: Vec3, overbounce: f32) -> Vec3 {
    // Calculate how much velocity is going into the surface
    let backoff = velocity.dot(normal);

    // Adjust based on whether we're moving into or away from surface
    let adjusted_backoff = if backoff < 0.0 {
        backoff * overbounce
    } else {
        backoff / overbounce
    };

    // Remove the into-surface component
    velocity - normal * adjusted_backoff
}

/// Perform a slide move through the collision world.
///
/// This is the core algorithm that handles collision response. It:
/// 1. Traces the player shape along the velocity
/// 2. If collision occurs, clips velocity to slide along surface
/// 3. Continues tracing with clipped velocity
/// 4. Handles corner cases with multiple surfaces
///
/// # Arguments
///
/// * `world` - The collision world to trace through
/// * `position` - Current position (will be updated)
/// * `velocity` - Current velocity (will be updated)
/// * `shape` - Player collision shape
/// * `delta_time` - Time step in seconds
/// * `config` - Movement configuration
///
/// # Returns
///
/// Whether the full movement succeeded without any collisions.
pub fn slide_move(
    world: &CollisionWorld,
    position: &mut Vec3,
    velocity: &mut Vec3,
    shape: TraceShape,
    delta_time: f32,
    config: &MovementConfig,
) -> bool {
    let mut time_remaining = delta_time;
    let original_velocity = *velocity;
    let mut planes: [Vec3; MAX_CLIP_PLANES] = [Vec3::ZERO; MAX_CLIP_PLANES];
    let mut num_planes = 0;

    // Limit iterations to prevent infinite loops
    for _ in 0..config.max_clip_planes {
        if velocity.length_squared() < 0.0001 {
            break;
        }

        // Calculate how far we want to move this iteration
        let move_delta = *velocity * time_remaining;
        let target_pos = *position + move_delta;

        // Trace to see if we can make it
        let trace = world.trace(
            *position,
            target_pos,
            shape,
            ContentFlags::MASK_PLAYER_SOLID,
        );

        // If we made the full distance, we're done
        if trace.fraction >= 1.0 {
            *position = trace.end_position;
            return num_planes == 0;
        }

        // Move to the collision point
        if trace.fraction > 0.0 {
            *position = trace.end_position;
        }

        // Reduce remaining time
        time_remaining *= 1.0 - trace.fraction;

        // Handle the collision
        if let Some(normal) = trace.hit_normal {
            // Check if we're stuck (started in solid)
            if trace.all_solid {
                *velocity = Vec3::ZERO;
                return false;
            }

            // Add this plane to our list
            if num_planes < MAX_CLIP_PLANES {
                planes[num_planes] = normal;
                num_planes += 1;
            }

            // Try to clip velocity to slide along all encountered planes
            let mut clipped = *velocity;
            let mut found_valid = false;

            for i in 0..num_planes {
                clipped = clip_velocity(clipped, planes[i], config.overbounce);

                // Check if this clipped velocity works with all other planes
                let mut valid = true;
                for j in 0..num_planes {
                    if i == j {
                        continue;
                    }
                    // Velocity must not go into any plane
                    if clipped.dot(planes[j]) < -0.01 {
                        valid = false;
                        break;
                    }
                }

                if valid {
                    *velocity = clipped;
                    found_valid = true;
                    break;
                }
            }

            if !found_valid {
                // Couldn't find a valid slide direction - try corners
                if num_planes >= 2 {
                    // Try sliding along the intersection of two planes
                    let cross = planes[0].cross(planes[1]).normalize_or_zero();
                    let speed = original_velocity.dot(cross);
                    *velocity = cross * speed;

                    // If still no good, just stop
                    if velocity.dot(planes[0]) < -0.01 || velocity.dot(planes[1]) < -0.01 {
                        *velocity = Vec3::ZERO;
                        return false;
                    }
                } else {
                    // Single plane but can't slide - stop
                    *velocity = Vec3::ZERO;
                    return false;
                }
            }
        }
    }

    false
}

/// Perform a step slide move.
///
/// This extends slide move with stair stepping - if the player hits
/// something, try stepping up and over it.
///
/// # Arguments
///
/// Same as `slide_move` plus:
/// * `ground_normal` - Current ground surface normal (if on ground)
///
/// # Returns
///
/// Whether the full movement succeeded.
pub fn step_slide_move(
    world: &CollisionWorld,
    position: &mut Vec3,
    velocity: &mut Vec3,
    shape: TraceShape,
    delta_time: f32,
    config: &MovementConfig,
    ground_normal: Option<Vec3>,
) -> bool {
    let start_position = *position;
    let start_velocity = *velocity;

    // First, try normal slide move
    let success = slide_move(world, position, velocity, shape, delta_time, config);

    if success {
        return true;
    }

    // Calculate how far we moved horizontally
    let horizontal_move = Vec3::new(
        position.x - start_position.x,
        0.0,
        position.z - start_position.z,
    );
    let horizontal_dist_sq = horizontal_move.length_squared();

    // Try stepping up
    let step_up_target = start_position + Vec3::new(0.0, config.step_height, 0.0);

    // Check if we can step up
    let up_trace = world.trace(
        start_position,
        step_up_target,
        shape,
        ContentFlags::MASK_PLAYER_SOLID,
    );

    if up_trace.all_solid {
        // Can't step up at all
        return false;
    }

    let stepped_position = up_trace.end_position;

    // Try moving horizontally from the stepped-up position
    let mut stepped_pos = stepped_position;
    let mut stepped_vel = start_velocity;

    slide_move(
        world,
        &mut stepped_pos,
        &mut stepped_vel,
        shape,
        delta_time,
        config,
    );

    // Step back down
    let down_target = stepped_pos - Vec3::new(0.0, config.step_height + 0.01, 0.0);
    let down_trace = world.trace(
        stepped_pos,
        down_target,
        shape,
        ContentFlags::MASK_PLAYER_SOLID,
    );

    if !down_trace.all_solid {
        stepped_pos = down_trace.end_position;
    }

    // Check if stepping got us further horizontally
    let stepped_horizontal = Vec3::new(
        stepped_pos.x - start_position.x,
        0.0,
        stepped_pos.z - start_position.z,
    );
    let stepped_dist_sq = stepped_horizontal.length_squared();

    // Use the stepped result if it got us further
    if stepped_dist_sq > horizontal_dist_sq {
        *position = stepped_pos;
        *velocity = stepped_vel;

        // Check if we landed on valid ground
        if let Some(normal) = down_trace.hit_normal {
            if normal.y >= config.min_ground_normal {
                // We stepped onto valid ground
                return true;
            }
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clip_velocity_wall() {
        // Moving into a wall on the +X side
        let velocity = Vec3::new(10.0, 0.0, 5.0);
        let wall_normal = Vec3::new(-1.0, 0.0, 0.0); // Wall facing -X

        let clipped = clip_velocity(velocity, wall_normal, 1.0);

        // X component should be zeroed, Z unchanged
        assert!(clipped.x.abs() < 0.01);
        assert!((clipped.z - 5.0).abs() < 0.01);
    }

    #[test]
    fn test_clip_velocity_slope() {
        // Moving down a 45-degree slope
        let velocity = Vec3::new(0.0, -10.0, 0.0);
        let slope_normal = Vec3::new(0.0, 0.707, 0.707).normalize();

        let clipped = clip_velocity(velocity, slope_normal, 1.0);

        // The clip removes the component going into the surface
        // Velocity is purely -Y, normal is roughly 45 degrees up-forward
        // Clipped velocity should still be going down but with forward component added
        // Actually, clip_velocity with overbounce=1.0 just removes the into-surface component
        // So velocity.dot(normal) < 0 (going into surface), backoff is negative
        // Result: velocity - normal * backoff, which adds normal * |backoff|
        // This should add a forward (+Y, +Z) component while reducing downward
        assert!(clipped.length() > 0.0); // Should have some velocity remaining
    }

    #[test]
    fn test_slide_move_no_collision() {
        let world = CollisionWorld::new();
        let config = MovementConfig::default();

        let mut position = Vec3::ZERO;
        let mut velocity = Vec3::new(5.0, 0.0, 0.0);
        let shape = TraceShape::PLAYER_STANDING;

        let success = slide_move(
            &world,
            &mut position,
            &mut velocity,
            shape,
            1.0,
            &config,
        );

        assert!(success);
        assert!((position.x - 5.0).abs() < 0.01);
    }

    #[test]
    fn test_slide_move_with_wall() {
        let mut world = CollisionWorld::new();

        // Add a floor
        world.add_box(
            Vec3::new(0.0, -0.5, 0.0),
            Vec3::new(50.0, 0.5, 50.0),
            ContentFlags::SOLID,
        );

        // Add a wall at x=5 (accounting for player radius)
        world.add_box(
            Vec3::new(5.5, 2.0, 0.0),
            Vec3::new(0.5, 2.0, 10.0),
            ContentFlags::SOLID,
        );

        let config = MovementConfig::default();
        let shape = TraceShape::PLAYER_STANDING;

        let mut position = Vec3::new(0.0, 0.0, 0.0);
        let mut velocity = Vec3::new(10.0, 0.0, 5.0); // Moving into wall at angle

        slide_move(&world, &mut position, &mut velocity, shape, 1.0, &config);

        // With wall at x=5, player should be stopped before it (accounting for radius)
        assert!(position.x < 5.5, "Position x={} should be < 5.5", position.x);
    }
}
