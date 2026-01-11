//! Collision world containing all static and dynamic geometry.
//!
//! The collision world stores all collidable geometry and provides efficient
//! trace queries through it.

use glam::Vec3;
use parry3d::math::{Isometry, Point, Real, Vector};
use parry3d::query::{Ray, contact};
use parry3d::shape::{Capsule, Cuboid, ConvexPolyhedron, Shape, SharedShape, TriMesh};

use super::flags::{ContentFlags, SurfaceFlags};
use super::trace::{TraceResult, TraceShape};

/// A piece of collision geometry in the world.
#[derive(Debug, Clone)]
pub struct CollisionBrush {
    /// Unique identifier for this brush.
    pub id: u32,
    /// The collision shape.
    pub shape: SharedShape,
    /// Position and orientation in world space.
    pub transform: Isometry<Real>,
    /// Content flags (solid, water, trigger, etc.).
    pub contents: ContentFlags,
    /// Surface flags (metal, wood, slick, etc.).
    pub surface: SurfaceFlags,
}

/// The collision world containing all geometry.
///
/// Supports:
/// - Box brushes (axis-aligned and oriented)
/// - Convex hull brushes
/// - Triangle mesh collision
///
/// # Thread Safety
///
/// The collision world is immutable after construction and can be safely
/// shared across threads for parallel traces.
#[derive(Debug, Default)]
pub struct CollisionWorld {
    /// Static world brushes (walls, floors, etc.).
    brushes: Vec<CollisionBrush>,
    /// Next brush ID to assign.
    next_id: u32,
}

impl CollisionWorld {
    /// Create an empty collision world.
    pub fn new() -> Self {
        Self {
            brushes: Vec::new(),
            next_id: 0,
        }
    }

    /// Add an axis-aligned box to the world.
    ///
    /// # Arguments
    ///
    /// * `center` - Center position of the box in world space
    /// * `half_extents` - Half-size in each axis (x, y, z)
    /// * `contents` - Content flags for collision filtering
    pub fn add_box(
        &mut self,
        center: Vec3,
        half_extents: Vec3,
        contents: ContentFlags,
    ) -> u32 {
        let id = self.next_id;
        self.next_id += 1;

        let shape = SharedShape::cuboid(half_extents.x, half_extents.y, half_extents.z);

        let transform = Isometry::translation(center.x, center.y, center.z);

        self.brushes.push(CollisionBrush {
            id,
            shape,
            transform,
            contents,
            surface: SurfaceFlags::NONE,
        });

        id
    }

    /// Add a convex hull to the world.
    ///
    /// # Arguments
    ///
    /// * `points` - Vertices defining the convex hull
    /// * `contents` - Content flags for collision filtering
    ///
    /// # Returns
    ///
    /// The brush ID, or `None` if the hull couldn't be computed.
    pub fn add_convex_hull(
        &mut self,
        points: &[Vec3],
        contents: ContentFlags,
    ) -> Option<u32> {
        let parry_points: Vec<Point<Real>> = points
            .iter()
            .map(|p| Point::new(p.x, p.y, p.z))
            .collect();

        let hull = ConvexPolyhedron::from_convex_hull(&parry_points)?;

        let id = self.next_id;
        self.next_id += 1;

        // SharedShape expects specific types, so we use convex_hull builder
        let shape = SharedShape::convex_hull(&parry_points)?;

        self.brushes.push(CollisionBrush {
            id,
            shape,
            transform: Isometry::identity(),
            contents,
            surface: SurfaceFlags::NONE,
        });

        Some(id)
    }

    /// Add a triangle mesh to the world.
    ///
    /// # Arguments
    ///
    /// * `vertices` - Mesh vertex positions
    /// * `indices` - Triangle indices (3 per triangle)
    /// * `contents` - Content flags for collision filtering
    pub fn add_triangle_mesh(
        &mut self,
        vertices: &[Vec3],
        indices: &[[u32; 3]],
        contents: ContentFlags,
    ) -> u32 {
        let parry_vertices: Vec<Point<Real>> = vertices
            .iter()
            .map(|v| Point::new(v.x, v.y, v.z))
            .collect();

        let id = self.next_id;
        self.next_id += 1;

        let shape = SharedShape::trimesh(parry_vertices, indices.to_vec())
            .expect("Failed to create trimesh");

        self.brushes.push(CollisionBrush {
            id,
            shape,
            transform: Isometry::identity(),
            contents,
            surface: SurfaceFlags::NONE,
        });

        id
    }

    /// Remove all collision geometry.
    pub fn clear(&mut self) {
        self.brushes.clear();
    }

    /// Get the number of collision brushes.
    pub fn brush_count(&self) -> usize {
        self.brushes.len()
    }

    /// Trace a shape through the world.
    ///
    /// This is the primary collision query. It sweeps the given shape from
    /// `start` to `end` and returns information about what was hit.
    ///
    /// # Arguments
    ///
    /// * `start` - Starting position (bottom-center of shape)
    /// * `end` - Desired end position
    /// * `shape` - The shape to trace (capsule, box, or point)
    /// * `mask` - Content flags to collide with
    pub fn trace(
        &self,
        start: Vec3,
        end: Vec3,
        shape: TraceShape,
        mask: ContentFlags,
    ) -> TraceResult {
        let delta = end - start;
        let distance = delta.length();

        // No movement - just check if position is valid
        if distance < 0.0001 {
            return if self.point_in_solid(start, shape, mask) {
                TraceResult {
                    fraction: 0.0,
                    end_position: start,
                    hit_normal: Some(Vec3::Y),
                    hit_contents: ContentFlags::SOLID,
                    hit_surface: SurfaceFlags::NONE,
                    started_in_solid: true,
                    all_solid: true,
                    hit_entity: -1,
                }
            } else {
                TraceResult::no_hit(start)
            };
        }

        let direction = delta / distance;

        // Use binary search for accurate collision detection
        self.trace_binary_search(start, end, shape, mask, distance, direction)
    }

    /// Perform a raycast (point trace) through the world.
    ///
    /// # Arguments
    ///
    /// * `origin` - Ray starting position
    /// * `direction` - Ray direction (will be normalized)
    /// * `max_distance` - Maximum trace distance
    /// * `mask` - Content flags to collide with
    pub fn raycast(
        &self,
        origin: Vec3,
        direction: Vec3,
        max_distance: f32,
        mask: ContentFlags,
    ) -> TraceResult {
        let dir = direction.normalize_or_zero();
        if dir.length_squared() < 0.5 {
            return TraceResult::no_hit(origin);
        }

        let ray = Ray::new(
            Point::new(origin.x, origin.y, origin.z),
            Vector::new(dir.x, dir.y, dir.z),
        );

        let mut closest_hit: Option<(f32, Vec3, &CollisionBrush)> = None;

        for brush in &self.brushes {
            // Check content mask
            if !mask.intersects(brush.contents) {
                continue;
            }

            // Cast ray against this brush
            if let Some(toi) = brush.shape.cast_ray(&brush.transform, &ray, max_distance, true) {
                if toi < max_distance {
                    let is_closer = closest_hit
                        .as_ref()
                        .map_or(true, |(dist, _, _)| toi < *dist);

                    if is_closer {
                        // Calculate hit normal
                        let hit_point = ray.point_at(toi);
                        let normal = self.compute_hit_normal(&ray, toi, brush);
                        closest_hit = Some((toi, normal, brush));
                    }
                }
            }
        }

        if let Some((distance, normal, brush)) = closest_hit {
            let fraction = distance / max_distance;
            let end_pos = origin + dir * distance;

            TraceResult {
                fraction,
                end_position: end_pos,
                hit_normal: Some(normal),
                hit_contents: brush.contents,
                hit_surface: brush.surface,
                started_in_solid: false,
                all_solid: false,
                hit_entity: -1,
            }
        } else {
            TraceResult::no_hit(origin + dir * max_distance)
        }
    }

    /// Check if a point (with shape) is inside solid geometry.
    pub fn point_in_solid(
        &self,
        position: Vec3,
        shape: TraceShape,
        mask: ContentFlags,
    ) -> bool {
        let test_shape = self.create_parry_shape(shape);
        let test_transform = self.shape_transform(position, shape);

        for brush in &self.brushes {
            if !mask.intersects(brush.contents) {
                continue;
            }

            // Check for intersection
            let prediction = 0.0; // No prediction distance
            if let Ok(Some(_)) = contact(
                &test_transform,
                test_shape.as_ref(),
                &brush.transform,
                brush.shape.as_ref(),
                prediction,
            ) {
                return true;
            }
        }

        false
    }

    /// Resolve collision by pushing shape out of solid geometry.
    ///
    /// Returns the corrected position.
    pub fn resolve_penetration(
        &self,
        position: Vec3,
        shape: TraceShape,
        mask: ContentFlags,
    ) -> Vec3 {
        let test_shape = self.create_parry_shape(shape);
        let test_transform = self.shape_transform(position, shape);

        let mut correction = Vec3::ZERO;

        for brush in &self.brushes {
            if !mask.intersects(brush.contents) {
                continue;
            }

            // Check for penetration
            if let Ok(Some(contact_result)) = contact(
                &test_transform,
                test_shape.as_ref(),
                &brush.transform,
                brush.shape.as_ref(),
                0.0,
            ) {
                // Push out along the contact normal
                let normal = Vec3::new(
                    contact_result.normal1.x,
                    contact_result.normal1.y,
                    contact_result.normal1.z,
                );
                let depth = -contact_result.dist; // Negative dist means penetration
                if depth > 0.0 {
                    correction += normal * (depth + 0.001); // Small epsilon
                }
            }
        }

        position + correction
    }

    // ========================================================================
    // Private helpers
    // ========================================================================

    /// Binary search trace for accurate collision detection.
    fn trace_binary_search(
        &self,
        start: Vec3,
        end: Vec3,
        shape: TraceShape,
        mask: ContentFlags,
        distance: f32,
        direction: Vec3,
    ) -> TraceResult {
        // Check if start position is in solid
        let start_in_solid = self.point_in_solid(start, shape, mask);

        // Check if end position is clear
        if !self.point_in_solid(end, shape, mask) {
            // Full path is clear
            return TraceResult {
                fraction: 1.0,
                end_position: end,
                hit_normal: None,
                hit_contents: ContentFlags::EMPTY,
                hit_surface: SurfaceFlags::NONE,
                started_in_solid: start_in_solid,
                all_solid: false,
                hit_entity: -1,
            };
        }

        // Binary search to find collision point
        let mut lo = 0.0_f32;
        let mut hi = 1.0_f32;

        for _ in 0..12 {
            // 12 iterations gives ~0.025% precision
            let mid = (lo + hi) * 0.5;
            let test_pos = start + (end - start) * mid;

            if self.point_in_solid(test_pos, shape, mask) {
                hi = mid;
            } else {
                lo = mid;
            }
        }

        let fraction = lo;
        let end_position = start + (end - start) * fraction;

        // Compute hit normal from penetration direction
        let penetration_test = start + (end - start) * hi;
        let resolved = self.resolve_penetration(penetration_test, shape, mask);
        let push = resolved - penetration_test;
        let hit_normal = if push.length_squared() > 0.0001 {
            push.normalize()
        } else {
            // Default to opposite of movement direction (projected to horizontal)
            let horizontal = Vec3::new(-direction.x, 0.0, -direction.z);
            if horizontal.length_squared() > 0.1 {
                horizontal.normalize()
            } else {
                Vec3::Y
            }
        };

        TraceResult {
            fraction,
            end_position,
            hit_normal: Some(hit_normal),
            hit_contents: ContentFlags::SOLID,
            hit_surface: SurfaceFlags::NONE,
            started_in_solid: start_in_solid,
            all_solid: start_in_solid && fraction < 0.001,
            hit_entity: -1,
        }
    }

    /// Create a parry3d shape from our TraceShape.
    fn create_parry_shape(&self, shape: TraceShape) -> SharedShape {
        match shape {
            TraceShape::Capsule { radius, height } => {
                // Parry capsule is defined by half-height of the cylinder part
                let cylinder_half_height = (height - 2.0 * radius).max(0.0) / 2.0;
                SharedShape::capsule_y(cylinder_half_height, radius)
            }
            TraceShape::Box { half_extents } => {
                SharedShape::cuboid(half_extents.x, half_extents.y, half_extents.z)
            }
            TraceShape::Point => {
                // Use a tiny sphere for point traces
                SharedShape::ball(0.001)
            }
        }
    }

    /// Create transform for a shape at a position.
    fn shape_transform(&self, position: Vec3, shape: TraceShape) -> Isometry<Real> {
        // Position is at the bottom-center of the shape
        let offset_y = match shape {
            TraceShape::Capsule { height, .. } => height / 2.0,
            TraceShape::Box { half_extents } => half_extents.y,
            TraceShape::Point => 0.0,
        };

        Isometry::translation(position.x, position.y + offset_y, position.z)
    }

    /// Compute hit normal from a ray intersection.
    fn compute_hit_normal(&self, ray: &Ray, toi: f32, brush: &CollisionBrush) -> Vec3 {
        // Try to get the normal from the shape
        if let Some(intersection) = brush.shape.cast_ray_and_get_normal(
            &brush.transform,
            ray,
            toi + 0.01,
            true,
        ) {
            Vec3::new(intersection.normal.x, intersection.normal.y, intersection.normal.z)
        } else {
            // Fallback: compute from ray direction
            let dir = Vec3::new(ray.dir.x, ray.dir.y, ray.dir.z);
            -dir.normalize()
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
            Vec3::new(50.0, 0.5, 50.0),
            ContentFlags::SOLID,
        );

        // Wall at x=10
        world.add_box(
            Vec3::new(10.0, 2.5, 0.0),
            Vec3::new(0.5, 2.5, 10.0),
            ContentFlags::SOLID,
        );

        world
    }

    #[test]
    fn test_raycast_hit() {
        let world = create_test_world();

        let result = world.raycast(
            Vec3::new(0.0, 1.0, 0.0),
            Vec3::X,
            100.0,
            ContentFlags::SOLID,
        );

        assert!(result.hit_something());
        assert!(result.fraction < 1.0);
        // Should hit wall at approximately x=9.5
        assert!((result.end_position.x - 9.5).abs() < 0.1);
    }

    #[test]
    fn test_raycast_miss() {
        let world = create_test_world();

        let result = world.raycast(
            Vec3::new(0.0, 1.0, 0.0),
            -Vec3::X,
            100.0,
            ContentFlags::SOLID,
        );

        // Should not hit anything going -X
        assert!(!result.hit_something());
        assert_eq!(result.fraction, 1.0);
    }

    #[test]
    fn test_trace_capsule() {
        let world = create_test_world();

        let shape = TraceShape::Capsule {
            radius: 0.4,
            height: 1.8,
        };

        // Trace towards wall
        let result = world.trace(
            Vec3::new(0.0, 0.0, 0.0),
            Vec3::new(15.0, 0.0, 0.0),
            shape,
            ContentFlags::SOLID,
        );

        assert!(result.hit_something());
        // Should stop before the wall
        assert!(result.end_position.x < 10.0);
    }

    #[test]
    fn test_point_in_solid() {
        let world = create_test_world();

        let shape = TraceShape::Point;

        // Inside floor
        assert!(world.point_in_solid(
            Vec3::new(0.0, -0.25, 0.0),
            shape,
            ContentFlags::SOLID,
        ));

        // Above floor
        assert!(!world.point_in_solid(
            Vec3::new(0.0, 1.0, 0.0),
            shape,
            ContentFlags::SOLID,
        ));
    }

    #[test]
    fn test_content_mask_filtering() {
        let mut world = CollisionWorld::new();

        // Add solid wall
        world.add_box(
            Vec3::new(5.0, 1.0, 0.0),
            Vec3::new(0.5, 1.0, 5.0),
            ContentFlags::SOLID,
        );

        // Add trigger (non-solid)
        world.add_box(
            Vec3::new(3.0, 1.0, 0.0),
            Vec3::new(0.5, 1.0, 5.0),
            ContentFlags::TRIGGER,
        );

        // Raycast with SOLID mask should ignore trigger
        let result = world.raycast(
            Vec3::new(0.0, 1.0, 0.0),
            Vec3::X,
            100.0,
            ContentFlags::SOLID,
        );

        assert!(result.hit_something());
        // Should hit wall at x=4.5, not trigger at x=2.5
        assert!((result.end_position.x - 4.5).abs() < 0.1);
    }
}
