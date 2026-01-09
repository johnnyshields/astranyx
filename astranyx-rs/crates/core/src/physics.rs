//! Physics utilities for the simulation.
//!
//! Simple 2D physics - no external physics engine needed for a shmup.

use glam::Vec2;

/// World bounds for the game area.
#[derive(Debug, Clone, Copy)]
pub struct WorldBounds {
    pub min: Vec2,
    pub max: Vec2,
}

impl WorldBounds {
    pub const fn new(min_x: f32, min_y: f32, max_x: f32, max_y: f32) -> Self {
        Self {
            min: Vec2::new(min_x, min_y),
            max: Vec2::new(max_x, max_y),
        }
    }

    /// Check if a point is within bounds.
    pub fn contains(&self, point: Vec2) -> bool {
        point.x >= self.min.x
            && point.x <= self.max.x
            && point.y >= self.min.y
            && point.y <= self.max.y
    }

    /// Check if a point with radius is completely outside bounds.
    pub fn is_outside(&self, point: Vec2, radius: f32) -> bool {
        point.x + radius < self.min.x
            || point.x - radius > self.max.x
            || point.y + radius < self.min.y
            || point.y - radius > self.max.y
    }

    /// Clamp a point to within bounds.
    pub fn clamp(&self, point: Vec2) -> Vec2 {
        Vec2::new(
            point.x.clamp(self.min.x, self.max.x),
            point.y.clamp(self.min.y, self.max.y),
        )
    }

    /// Clamp a point with radius padding.
    pub fn clamp_with_radius(&self, point: Vec2, radius: f32) -> Vec2 {
        Vec2::new(
            point.x.clamp(self.min.x + radius, self.max.x - radius),
            point.y.clamp(self.min.y + radius, self.max.y - radius),
        )
    }

    pub fn width(&self) -> f32 {
        self.max.x - self.min.x
    }

    pub fn height(&self) -> f32 {
        self.max.y - self.min.y
    }

    pub fn center(&self) -> Vec2 {
        (self.min + self.max) * 0.5
    }
}

impl Default for WorldBounds {
    fn default() -> Self {
        // 16:9 aspect ratio game area
        Self::new(0.0, 0.0, 1920.0, 1080.0)
    }
}

/// Circle-circle collision detection.
#[inline]
pub fn circles_collide(pos_a: Vec2, radius_a: f32, pos_b: Vec2, radius_b: f32) -> bool {
    let distance_sq = pos_a.distance_squared(pos_b);
    let combined_radius = radius_a + radius_b;
    distance_sq <= combined_radius * combined_radius
}

/// Point-circle collision detection.
#[inline]
pub fn point_in_circle(point: Vec2, circle_center: Vec2, radius: f32) -> bool {
    point.distance_squared(circle_center) <= radius * radius
}

/// Rectangle-rectangle collision detection (AABB).
#[inline]
pub fn rects_collide(
    pos_a: Vec2,
    half_size_a: Vec2,
    pos_b: Vec2,
    half_size_b: Vec2,
) -> bool {
    let diff = (pos_a - pos_b).abs();
    let combined = half_size_a + half_size_b;
    diff.x <= combined.x && diff.y <= combined.y
}

/// Linear interpolation.
#[inline]
pub fn lerp(a: f32, b: f32, t: f32) -> f32 {
    a + (b - a) * t
}

/// Smoothstep interpolation.
#[inline]
pub fn smoothstep(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    t * t * (3.0 - 2.0 * t)
}

/// Move towards a target value at a maximum delta.
#[inline]
pub fn move_towards(current: f32, target: f32, max_delta: f32) -> f32 {
    let diff = target - current;
    if diff.abs() <= max_delta {
        target
    } else {
        current + diff.signum() * max_delta
    }
}

/// Move a vector towards a target at a maximum delta.
#[inline]
pub fn move_towards_vec2(current: Vec2, target: Vec2, max_delta: f32) -> Vec2 {
    let diff = target - current;
    let dist = diff.length();
    if dist <= max_delta || dist == 0.0 {
        target
    } else {
        current + diff / dist * max_delta
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn circle_collision() {
        assert!(circles_collide(
            Vec2::ZERO,
            10.0,
            Vec2::new(15.0, 0.0),
            10.0
        ));
        assert!(!circles_collide(
            Vec2::ZERO,
            10.0,
            Vec2::new(25.0, 0.0),
            10.0
        ));
    }

    #[test]
    fn bounds_clamping() {
        let bounds = WorldBounds::new(0.0, 0.0, 100.0, 100.0);
        assert_eq!(bounds.clamp(Vec2::new(50.0, 50.0)), Vec2::new(50.0, 50.0));
        assert_eq!(bounds.clamp(Vec2::new(-10.0, 50.0)), Vec2::new(0.0, 50.0));
        assert_eq!(bounds.clamp(Vec2::new(150.0, 150.0)), Vec2::new(100.0, 100.0));
    }

    #[test]
    fn move_towards_value() {
        assert_eq!(move_towards(0.0, 10.0, 3.0), 3.0);
        assert_eq!(move_towards(8.0, 10.0, 3.0), 10.0);
        assert_eq!(move_towards(10.0, 0.0, 3.0), 7.0);
    }
}
