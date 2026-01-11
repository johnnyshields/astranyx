//! Trace results and shapes for collision queries.

use glam::Vec3;
use serde::{Deserialize, Serialize};

use super::flags::{ContentFlags, SurfaceFlags};

/// Result of a collision trace through the world.
///
/// Traces sweep a shape from a start position to an end position and
/// report what was hit along the way.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceResult {
    /// How far along the trace path we got before hitting something.
    ///
    /// - `1.0` = traveled the full distance (no collision)
    /// - `0.0` = hit something immediately at start
    /// - `0.5` = hit something halfway through
    pub fraction: f32,

    /// Final position after the trace.
    ///
    /// If `fraction < 1.0`, this is slightly backed off from the impact point
    /// to prevent floating-point precision issues.
    pub end_position: Vec3,

    /// Surface normal at the impact point.
    ///
    /// Points away from the surface that was hit. `None` if no collision
    /// occurred (`fraction == 1.0`).
    pub hit_normal: Option<Vec3>,

    /// Content flags of what was hit.
    pub hit_contents: ContentFlags,

    /// Surface flags of the hit surface.
    pub hit_surface: SurfaceFlags,

    /// Whether the trace started inside solid geometry.
    ///
    /// This can happen when the player clips into a wall. Movement code
    /// should try to push the player out when this is true.
    pub started_in_solid: bool,

    /// Whether the entire trace was inside solid geometry.
    ///
    /// More severe than `started_in_solid` - the trace couldn't move at all.
    pub all_solid: bool,

    /// Entity ID that was hit (if any).
    ///
    /// -1 means world geometry, >= 0 means an entity.
    pub hit_entity: i32,
}

impl Default for TraceResult {
    fn default() -> Self {
        Self::no_hit(Vec3::ZERO)
    }
}

impl TraceResult {
    /// Create a trace result indicating no collision occurred.
    pub fn no_hit(end_position: Vec3) -> Self {
        Self {
            fraction: 1.0,
            end_position,
            hit_normal: None,
            hit_contents: ContentFlags::EMPTY,
            hit_surface: SurfaceFlags::NONE,
            started_in_solid: false,
            all_solid: false,
            hit_entity: -1,
        }
    }

    /// Create a trace result indicating a collision occurred.
    pub fn hit(fraction: f32, end_position: Vec3, normal: Vec3) -> Self {
        Self {
            fraction,
            end_position,
            hit_normal: Some(normal),
            hit_contents: ContentFlags::SOLID,
            hit_surface: SurfaceFlags::NONE,
            started_in_solid: false,
            all_solid: false,
            hit_entity: -1,
        }
    }

    /// Check if this trace hit something.
    #[inline]
    pub fn hit_something(&self) -> bool {
        self.fraction < 1.0
    }

    /// Get the hit normal, defaulting to up if none.
    #[inline]
    pub fn normal_or_up(&self) -> Vec3 {
        self.hit_normal.unwrap_or(Vec3::Y)
    }
}

/// Shape used for collision traces.
///
/// The physics engine supports two primary shapes for player collision:
///
/// - **Capsule**: A vertical pill shape (cylinder with hemisphere caps). Best for
///   player collision as it handles slopes and stairs smoothly.
///
/// - **Box**: An axis-aligned bounding box. Simpler and faster, good for
///   projectiles and simple entities.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum TraceShape {
    /// A vertical capsule (pill shape).
    ///
    /// Defined by radius and total height. The capsule is centered vertically
    /// on the trace origin, so half the height extends above and below.
    Capsule {
        /// Radius of the capsule cylinder and end caps.
        radius: f32,
        /// Total height from bottom of lower cap to top of upper cap.
        height: f32,
    },

    /// An axis-aligned bounding box.
    ///
    /// Defined by half-extents from the center in each axis.
    Box {
        /// Half-size in each axis (x, y, z).
        half_extents: Vec3,
    },

    /// A single point (infinitely small).
    ///
    /// Used for ray traces like bullet hits or line-of-sight checks.
    Point,
}

impl TraceShape {
    /// Create a standing player capsule.
    pub const PLAYER_STANDING: Self = Self::Capsule {
        radius: 0.4,   // 40cm radius
        height: 1.8,   // 180cm tall
    };

    /// Create a crouching player capsule.
    pub const PLAYER_CROUCHING: Self = Self::Capsule {
        radius: 0.4,   // 40cm radius
        height: 1.0,   // 100cm tall when crouched
    };

    /// Get the effective radius of this shape for collision purposes.
    pub fn radius(&self) -> f32 {
        match self {
            Self::Capsule { radius, .. } => *radius,
            Self::Box { half_extents } => half_extents.x.max(half_extents.z),
            Self::Point => 0.0,
        }
    }

    /// Get the height of this shape.
    pub fn height(&self) -> f32 {
        match self {
            Self::Capsule { height, .. } => *height,
            Self::Box { half_extents } => half_extents.y * 2.0,
            Self::Point => 0.0,
        }
    }

    /// Get a bounding box that fully contains this shape.
    pub fn bounding_box(&self) -> (Vec3, Vec3) {
        match self {
            Self::Capsule { radius, height } => {
                let half_height = height / 2.0;
                (
                    Vec3::new(-*radius, -half_height, -*radius),
                    Vec3::new(*radius, half_height, *radius),
                )
            }
            Self::Box { half_extents } => (-*half_extents, *half_extents),
            Self::Point => (Vec3::ZERO, Vec3::ZERO),
        }
    }

    /// Check if this is a point trace (raycast).
    #[inline]
    pub fn is_point(&self) -> bool {
        matches!(self, Self::Point)
    }
}

impl Default for TraceShape {
    fn default() -> Self {
        Self::PLAYER_STANDING
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trace_result_no_hit() {
        let result = TraceResult::no_hit(Vec3::new(10.0, 0.0, 0.0));
        assert!(!result.hit_something());
        assert_eq!(result.fraction, 1.0);
        assert!(result.hit_normal.is_none());
    }

    #[test]
    fn test_trace_result_hit() {
        let result = TraceResult::hit(0.5, Vec3::new(5.0, 0.0, 0.0), Vec3::X);
        assert!(result.hit_something());
        assert_eq!(result.fraction, 0.5);
        assert_eq!(result.hit_normal, Some(Vec3::X));
    }

    #[test]
    fn test_trace_shape_bounding_box() {
        let capsule = TraceShape::Capsule {
            radius: 0.5,
            height: 2.0,
        };
        let (min, max) = capsule.bounding_box();
        assert_eq!(min, Vec3::new(-0.5, -1.0, -0.5));
        assert_eq!(max, Vec3::new(0.5, 1.0, 0.5));
    }
}
