//! Level mesh types for glTF-based level loading.
//!
//! Separates visual meshes (for rendering) from collision meshes (for physics).
//! Collision meshes use parry3d for efficient queries.

use glam::Vec3;
use parry3d::shape::SharedShape;
use parry3d::math::{Point, Isometry};
use parry3d::query;
use parry3d::bounding_volume::Aabb;
use parry3d::na;  // nalgebra re-export

/// A complete level loaded from a glTF file.
#[derive(Debug)]
pub struct LevelMesh {
    /// Visual meshes for rendering (name, vertices, indices, transform).
    pub render_meshes: Vec<RenderMesh>,
    /// Collision shapes for physics.
    pub collision_world: CollisionWorld,
    /// Light sources defined in the level.
    pub lights: Vec<LevelLight>,
}

/// A single mesh for rendering.
#[derive(Debug, Clone)]
pub struct RenderMesh {
    /// Unique name from glTF.
    pub name: String,
    /// Vertex positions.
    pub positions: Vec<Vec3>,
    /// Vertex normals.
    pub normals: Vec<Vec3>,
    /// Triangle indices.
    pub indices: Vec<u32>,
    /// Transform (position, rotation, scale).
    pub transform: MeshTransform,
    /// Base color (from material or default).
    pub color: [u8; 3],
}

/// Transform for a mesh instance.
#[derive(Debug, Clone, Copy, Default)]
pub struct MeshTransform {
    pub position: Vec3,
    pub rotation: Vec3,  // Euler angles in radians
    pub scale: Vec3,
}

impl MeshTransform {
    pub fn new() -> Self {
        Self {
            position: Vec3::ZERO,
            rotation: Vec3::ZERO,
            scale: Vec3::ONE,
        }
    }

    pub fn with_position(mut self, pos: Vec3) -> Self {
        self.position = pos;
        self
    }

    pub fn with_scale(mut self, scale: Vec3) -> Self {
        self.scale = scale;
        self
    }
}

/// A light source in the level.
#[derive(Debug, Clone)]
pub struct LevelLight {
    pub name: String,
    pub light_type: LevelLightType,
    pub position: Vec3,
    pub color: [u8; 3],
    pub intensity: f32,
    pub range: f32,
}

/// Light types supported in levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LevelLightType {
    Point,
    Spot { angle: u32 },  // Angle in degrees
    Directional,
}

/// Collision world containing all static collision shapes.
#[derive(Debug)]
pub struct CollisionWorld {
    /// Individual collision shapes with their transforms.
    shapes: Vec<CollisionShape>,
    /// Combined trimesh for efficient queries (built from all shapes).
    combined_mesh: Option<SharedShape>,
}

impl Default for CollisionWorld {
    fn default() -> Self {
        Self::new()
    }
}

impl CollisionWorld {
    pub fn new() -> Self {
        Self {
            shapes: Vec::new(),
            combined_mesh: None,
        }
    }

    /// Add a collision shape.
    pub fn add_shape(&mut self, shape: CollisionShape) {
        self.shapes.push(shape);
        // Invalidate combined mesh - will be rebuilt on next query
        self.combined_mesh = None;
    }

    /// Add a box collision shape.
    pub fn add_box(&mut self, name: &str, center: Vec3, half_extents: Vec3) {
        self.add_shape(CollisionShape::Box {
            name: name.to_string(),
            center,
            half_extents,
        });
    }

    /// Add a convex hull collision shape.
    pub fn add_convex_hull(&mut self, name: &str, vertices: Vec<Vec3>, transform: MeshTransform) {
        self.add_shape(CollisionShape::ConvexHull {
            name: name.to_string(),
            vertices,
            transform,
        });
    }

    /// Add a trimesh collision shape.
    pub fn add_trimesh(&mut self, name: &str, vertices: Vec<Vec3>, indices: Vec<[u32; 3]>, transform: MeshTransform) {
        self.add_shape(CollisionShape::Trimesh {
            name: name.to_string(),
            vertices,
            indices,
            transform,
        });
    }

    /// Get all shapes.
    pub fn shapes(&self) -> &[CollisionShape] {
        &self.shapes
    }

    /// Check if a point is inside any collision shape.
    pub fn point_inside(&self, point: Vec3) -> bool {
        let p = Point::new(point.x, point.y, point.z);

        for shape in &self.shapes {
            if shape.contains_point(p) {
                return true;
            }
        }
        false
    }

    /// Cast a ray and return the closest hit distance.
    pub fn raycast(&self, origin: Vec3, direction: Vec3, max_dist: f32) -> Option<f32> {
        let ray = parry3d::query::Ray::new(
            Point::new(origin.x, origin.y, origin.z),
            parry3d::math::Vector::new(direction.x, direction.y, direction.z),
        );

        let mut closest: Option<f32> = None;

        for shape in &self.shapes {
            if let Some(t) = shape.raycast(&ray, max_dist) {
                closest = Some(closest.map_or(t, |c| c.min(t)));
            }
        }

        closest
    }

    /// Resolve collision for a capsule (player).
    /// Returns the corrected position after sliding along surfaces.
    pub fn resolve_capsule_collision(
        &self,
        position: Vec3,
        radius: f32,
        height: f32,
    ) -> Vec3 {
        let mut resolved = position;

        for shape in &self.shapes {
            if let Some(penetration) = shape.capsule_penetration(resolved, radius, height) {
                resolved += penetration;
            }
        }

        resolved
    }
}

/// Individual collision shape types.
#[derive(Debug, Clone)]
pub enum CollisionShape {
    /// Axis-aligned box.
    Box {
        name: String,
        center: Vec3,
        half_extents: Vec3,
    },
    /// Convex hull from vertices.
    ConvexHull {
        name: String,
        vertices: Vec<Vec3>,
        transform: MeshTransform,
    },
    /// Triangle mesh (most flexible, slowest).
    Trimesh {
        name: String,
        vertices: Vec<Vec3>,
        indices: Vec<[u32; 3]>,
        transform: MeshTransform,
    },
}

impl CollisionShape {
    /// Get the shape name.
    pub fn name(&self) -> &str {
        match self {
            Self::Box { name, .. } => name,
            Self::ConvexHull { name, .. } => name,
            Self::Trimesh { name, .. } => name,
        }
    }

    /// Check if a point is inside this shape.
    fn contains_point(&self, point: Point<f32>) -> bool {
        match self {
            Self::Box { center, half_extents, .. } => {
                let min = Point::new(
                    center.x - half_extents.x,
                    center.y - half_extents.y,
                    center.z - half_extents.z,
                );
                let max = Point::new(
                    center.x + half_extents.x,
                    center.y + half_extents.y,
                    center.z + half_extents.z,
                );
                point.x >= min.x && point.x <= max.x &&
                point.y >= min.y && point.y <= max.y &&
                point.z >= min.z && point.z <= max.z
            }
            Self::ConvexHull { vertices, transform, .. } => {
                // Transform point to local space and check
                let local_point = self.world_to_local(point, transform);
                // Use parry3d convex hull point containment
                if let Some(hull) = self.build_convex_hull(vertices) {
                    hull.contains_local_point(&local_point)
                } else {
                    false
                }
            }
            Self::Trimesh { .. } => {
                // Trimesh containment is complex - for now return false
                // (trimeshes are usually thin surfaces, not volumes)
                false
            }
        }
    }

    /// Cast a ray against this shape.
    fn raycast(&self, ray: &parry3d::query::Ray, max_dist: f32) -> Option<f32> {
        match self {
            Self::Box { center, half_extents, .. } => {
                let aabb = Aabb::new(
                    Point::new(
                        center.x - half_extents.x,
                        center.y - half_extents.y,
                        center.z - half_extents.z,
                    ),
                    Point::new(
                        center.x + half_extents.x,
                        center.y + half_extents.y,
                        center.z + half_extents.z,
                    ),
                );
                aabb.clip_ray_parameters(ray)
                    .filter(|(t_min, t_max)| *t_min <= max_dist && *t_max >= 0.0)
                    .map(|(t_min, _)| t_min.max(0.0))
            }
            Self::ConvexHull { vertices, transform, .. } => {
                if let Some(hull) = self.build_convex_hull(vertices) {
                    let iso = self.transform_to_isometry(transform);
                    hull.cast_ray(&iso, ray, max_dist, true)
                        .map(|hit| hit)
                } else {
                    None
                }
            }
            Self::Trimesh { vertices, indices, transform, .. } => {
                if let Some(mesh) = self.build_trimesh(vertices, indices) {
                    let iso = self.transform_to_isometry(transform);
                    mesh.cast_ray(&iso, ray, max_dist, true)
                        .map(|hit| hit)
                } else {
                    None
                }
            }
        }
    }

    /// Calculate penetration vector for a capsule collision.
    fn capsule_penetration(&self, capsule_pos: Vec3, radius: f32, height: f32) -> Option<Vec3> {
        match self {
            Self::Box { center, half_extents, .. } => {
                // Expand box by capsule radius
                let expanded_half = Vec3::new(
                    half_extents.x + radius,
                    half_extents.y,
                    half_extents.z + radius,
                );

                // Check Y overlap (capsule bottom to top)
                let capsule_bottom = capsule_pos.y;
                let capsule_top = capsule_pos.y + height;
                let box_bottom = center.y - half_extents.y;
                let box_top = center.y + half_extents.y;

                if capsule_top < box_bottom || capsule_bottom > box_top {
                    return None;
                }

                // Check XZ containment in expanded box
                let in_x = capsule_pos.x >= center.x - expanded_half.x
                    && capsule_pos.x <= center.x + expanded_half.x;
                let in_z = capsule_pos.z >= center.z - expanded_half.z
                    && capsule_pos.z <= center.z + expanded_half.z;

                if in_x && in_z {
                    // Inside - find shortest push-out direction
                    let to_left = capsule_pos.x - (center.x - expanded_half.x);
                    let to_right = (center.x + expanded_half.x) - capsule_pos.x;
                    let to_back = capsule_pos.z - (center.z - expanded_half.z);
                    let to_front = (center.z + expanded_half.z) - capsule_pos.z;

                    let min_dist = to_left.min(to_right).min(to_back).min(to_front);

                    if min_dist == to_left {
                        Some(Vec3::new(-to_left, 0.0, 0.0))
                    } else if min_dist == to_right {
                        Some(Vec3::new(to_right, 0.0, 0.0))
                    } else if min_dist == to_back {
                        Some(Vec3::new(0.0, 0.0, -to_back))
                    } else {
                        Some(Vec3::new(0.0, 0.0, to_front))
                    }
                } else {
                    None
                }
            }
            Self::ConvexHull { vertices, transform, .. } => {
                // For convex hulls, use parry3d contact query
                if let Some(hull) = self.build_convex_hull(vertices) {
                    let capsule = parry3d::shape::Capsule::new_y(height / 2.0, radius);
                    let capsule_iso = Isometry::translation(capsule_pos.x, capsule_pos.y + height / 2.0, capsule_pos.z);
                    let hull_iso = self.transform_to_isometry(transform);

                    if let Ok(Some(contact)) = query::contact(&capsule_iso, &capsule, &hull_iso, hull.as_ref(), 0.0) {
                        let penetration = contact.dist.abs();
                        let normal = contact.normal1.into_inner();
                        Some(Vec3::new(normal.x, normal.y, normal.z) * penetration)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Self::Trimesh { vertices, indices, transform, .. } => {
                // For trimeshes, use parry3d contact query
                if let Some(mesh) = self.build_trimesh(vertices, indices) {
                    let capsule = parry3d::shape::Capsule::new_y(height / 2.0, radius);
                    let capsule_iso = Isometry::translation(capsule_pos.x, capsule_pos.y + height / 2.0, capsule_pos.z);
                    let mesh_iso = self.transform_to_isometry(transform);

                    if let Ok(Some(contact)) = query::contact(&capsule_iso, &capsule, &mesh_iso, mesh.as_ref(), 0.0) {
                        let penetration = contact.dist.abs();
                        let normal = contact.normal1.into_inner();
                        Some(Vec3::new(normal.x, normal.y, normal.z) * penetration)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }
    }

    // Helper methods

    fn world_to_local(&self, point: Point<f32>, transform: &MeshTransform) -> Point<f32> {
        // Simple inverse transform (ignoring rotation for now)
        Point::new(
            (point.x - transform.position.x) / transform.scale.x,
            (point.y - transform.position.y) / transform.scale.y,
            (point.z - transform.position.z) / transform.scale.z,
        )
    }

    fn transform_to_isometry(&self, transform: &MeshTransform) -> Isometry<f32> {
        // Create isometry from transform
        // Note: parry3d uses nalgebra types internally
        let translation = parry3d::math::Vector::new(
            transform.position.x,
            transform.position.y,
            transform.position.z,
        );
        Isometry::from_parts(
            translation.into(),
            na::UnitQuaternion::identity(), // TODO: Add rotation support
        )
    }

    fn build_convex_hull(&self, vertices: &[Vec3]) -> Option<SharedShape> {
        let points: Vec<Point<f32>> = vertices
            .iter()
            .map(|v| Point::new(v.x, v.y, v.z))
            .collect();

        SharedShape::convex_hull(&points)
    }

    fn build_trimesh(&self, vertices: &[Vec3], indices: &[[u32; 3]]) -> Option<SharedShape> {
        let points: Vec<Point<f32>> = vertices
            .iter()
            .map(|v| Point::new(v.x, v.y, v.z))
            .collect();

        Some(SharedShape::trimesh(points, indices.to_vec()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_box_collision() {
        let mut world = CollisionWorld::new();
        world.add_box("test_wall", Vec3::new(0.0, 5.0, 0.0), Vec3::new(10.0, 5.0, 1.0));

        // Point inside box
        assert!(world.point_inside(Vec3::new(0.0, 5.0, 0.0)));

        // Point outside box
        assert!(!world.point_inside(Vec3::new(20.0, 5.0, 0.0)));
    }

    #[test]
    fn test_raycast() {
        let mut world = CollisionWorld::new();
        world.add_box("test_wall", Vec3::new(10.0, 0.0, 0.0), Vec3::new(1.0, 10.0, 10.0));

        // Ray toward wall
        let hit = world.raycast(Vec3::ZERO, Vec3::X, 100.0);
        assert!(hit.is_some());
        assert!((hit.unwrap() - 9.0).abs() < 0.1);

        // Ray away from wall
        let miss = world.raycast(Vec3::ZERO, Vec3::NEG_X, 100.0);
        assert!(miss.is_none());
    }

    #[test]
    fn test_capsule_collision() {
        let mut world = CollisionWorld::new();
        world.add_box("test_wall", Vec3::new(0.0, 2.5, 0.0), Vec3::new(2.0, 2.5, 2.0));

        // Capsule intersecting box
        let resolved = world.resolve_capsule_collision(Vec3::new(0.0, 0.0, 0.0), 0.5, 1.8);

        // Should be pushed out
        assert!(resolved.length() > 0.0);
    }
}
