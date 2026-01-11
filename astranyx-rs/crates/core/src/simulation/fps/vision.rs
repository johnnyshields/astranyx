//! Vision cone system for enemy detection.
//!
//! Implements MGS-style vision with:
//! - Forward cone (narrow, long range)
//! - Peripheral vision (wide, short range)
//! - Line-of-sight checks (blocked by walls)
//! - Light level awareness (harder to see in shadows)
//!
//! Uses deterministic math functions for cross-platform consistency.

use glam::{Vec2, Vec3};

use crate::math::{atan2_det, length_det, normalize_angle_diff};

/// Vision cone configuration for an enemy.
#[derive(Debug, Clone)]
pub struct VisionCone {
    /// Forward vision distance (how far they can see ahead)
    pub forward_distance: f32,
    /// Forward vision half-angle in radians (typically ~30 degrees)
    pub forward_half_angle: f32,
    /// Peripheral vision distance (much shorter)
    pub peripheral_distance: f32,
    /// Peripheral vision half-angle in radians (typically ~80 degrees)
    pub peripheral_half_angle: f32,
    /// Height offset for eye position
    pub eye_height: f32,
}

impl Default for VisionCone {
    fn default() -> Self {
        Self {
            forward_distance: 200.0,
            forward_half_angle: 0.52, // ~30 degrees
            peripheral_distance: 50.0,
            peripheral_half_angle: 1.4, // ~80 degrees
            eye_height: 1.7,
        }
    }
}

impl VisionCone {
    /// Create a vision cone for a guard-type enemy (standard)
    pub fn guard() -> Self {
        Self::default()
    }

    /// Create a vision cone for a sniper-type enemy (long range, narrow)
    pub fn sniper() -> Self {
        Self {
            forward_distance: 400.0,
            forward_half_angle: 0.26, // ~15 degrees
            peripheral_distance: 30.0,
            peripheral_half_angle: 1.0,
            eye_height: 1.7,
        }
    }

    /// Create a vision cone for a patrol-type enemy (wide awareness)
    pub fn patrol() -> Self {
        Self {
            forward_distance: 150.0,
            forward_half_angle: 0.7, // ~40 degrees
            peripheral_distance: 80.0,
            peripheral_half_angle: 1.57, // ~90 degrees
            eye_height: 1.7,
        }
    }
}

/// Result of a vision check.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum VisionResult {
    /// Target not visible at all
    NotVisible,
    /// Target in peripheral vision (suspicious)
    Peripheral { distance: f32 },
    /// Target in forward cone (clear sight)
    FullySeen { distance: f32 },
}

impl VisionResult {
    pub fn is_visible(&self) -> bool {
        !matches!(self, VisionResult::NotVisible)
    }

    pub fn is_fully_seen(&self) -> bool {
        matches!(self, VisionResult::FullySeen { .. })
    }

    pub fn distance(&self) -> Option<f32> {
        match self {
            VisionResult::NotVisible => None,
            VisionResult::Peripheral { distance } | VisionResult::FullySeen { distance } => {
                Some(*distance)
            }
        }
    }
}

/// Check if a target is visible from an enemy's position.
///
/// # Arguments
/// * `enemy_pos` - Enemy position (3D)
/// * `enemy_yaw` - Enemy facing direction (yaw in radians)
/// * `target_pos` - Target position (3D)
/// * `vision` - Vision cone configuration
/// * `target_visibility` - How visible the target is (0.0 = invisible, 1.0 = fully visible)
///
/// # Returns
/// VisionResult indicating visibility status
pub fn check_vision(
    enemy_pos: Vec3,
    enemy_yaw: f32,
    target_pos: Vec3,
    vision: &VisionCone,
    target_visibility: f32,
) -> VisionResult {
    // Calculate eye position
    let eye_pos = enemy_pos + Vec3::new(0.0, vision.eye_height, 0.0);

    // Vector to target (in XZ plane for angle calculation)
    let to_target = target_pos - eye_pos;
    let to_target_flat = Vec2::new(to_target.x, to_target.z);

    // Use deterministic length calculation
    let distance = length_det(to_target_flat.x, to_target_flat.y);

    if distance < 0.1 {
        // Target is at same position (always visible)
        return VisionResult::FullySeen { distance: 0.0 };
    }

    // Calculate angle to target using deterministic atan2
    let target_angle = atan2_det(to_target_flat.y, to_target_flat.x);
    let enemy_forward_angle = enemy_yaw;

    // Normalize angle difference to [-PI, PI] using deterministic function
    let angle_diff = normalize_angle_diff(target_angle - enemy_forward_angle).abs();

    // Adjust distances based on target visibility (crouching, in shadow, etc.)
    let effective_forward_dist = vision.forward_distance * target_visibility;
    let effective_peripheral_dist = vision.peripheral_distance * target_visibility;

    // Check forward cone first
    if angle_diff <= vision.forward_half_angle && distance <= effective_forward_dist {
        return VisionResult::FullySeen { distance };
    }

    // Check peripheral vision
    if angle_diff <= vision.peripheral_half_angle && distance <= effective_peripheral_dist {
        return VisionResult::Peripheral { distance };
    }

    VisionResult::NotVisible
}

/// Simple ray-cast for line of sight check.
/// Returns true if there's a clear line of sight (no obstacles).
///
/// For now, this is a simple distance check. In a full implementation,
/// this would check against level geometry.
pub fn has_line_of_sight(from: Vec3, to: Vec3, _max_distance: f32) -> bool {
    // TODO: Implement actual raycasting against level geometry
    // For now, just check if target is within reasonable range
    let distance = (to - from).length();
    distance < 500.0
}

/// Calculate how visible a target is based on various factors.
///
/// # Arguments
/// * `is_crouching` - Target is crouching
/// * `is_prone` - Target is prone
/// * `is_moving` - Target is moving
/// * `light_level` - Ambient light (0.0 = dark, 1.0 = bright)
/// * `in_cover` - Target is behind cover
///
/// # Returns
/// Visibility multiplier (0.0 = invisible, 1.0 = fully visible)
pub fn calculate_visibility(
    is_crouching: bool,
    is_prone: bool,
    is_moving: bool,
    light_level: f32,
    in_cover: bool,
) -> f32 {
    let mut visibility = 1.0;

    // Posture affects visibility
    if is_prone {
        visibility *= 0.3;
    } else if is_crouching {
        visibility *= 0.6;
    }

    // Movement increases visibility
    if is_moving {
        visibility *= 1.5;
    }

    // Light level
    visibility *= light_level.clamp(0.1, 1.0);

    // Cover provides significant reduction
    if in_cover {
        visibility *= 0.2;
    }

    visibility.clamp(0.0, 2.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_forward_vision() {
        let vision = VisionCone::default();
        let enemy_pos = Vec3::new(0.0, 0.0, 0.0);
        let enemy_yaw = 0.0; // Facing +X

        // Target directly ahead
        let target = Vec3::new(100.0, 0.0, 0.0);
        let result = check_vision(enemy_pos, enemy_yaw, target, &vision, 1.0);
        assert!(result.is_fully_seen());

        // Target too far
        let target_far = Vec3::new(500.0, 0.0, 0.0);
        let result = check_vision(enemy_pos, enemy_yaw, target_far, &vision, 1.0);
        assert!(!result.is_visible());
    }

    #[test]
    fn test_peripheral_vision() {
        let vision = VisionCone::default();
        let enemy_pos = Vec3::new(0.0, 0.0, 0.0);
        let enemy_yaw = 0.0;

        // Target to the side, close
        let target = Vec3::new(10.0, 0.0, 40.0);
        let result = check_vision(enemy_pos, enemy_yaw, target, &vision, 1.0);
        assert!(matches!(result, VisionResult::Peripheral { .. }));
    }

    #[test]
    fn test_visibility_modifiers() {
        // Standing in bright light, moving
        let vis1 = calculate_visibility(false, false, true, 1.0, false);
        assert!(vis1 > 1.0);

        // Crouching in shadow, still
        let vis2 = calculate_visibility(true, false, false, 0.3, false);
        assert!(vis2 < 0.5);

        // Prone in cover
        let vis3 = calculate_visibility(false, true, false, 1.0, true);
        assert!(vis3 < 0.1);
    }
}
