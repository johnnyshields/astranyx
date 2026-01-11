//! FPS wall collision detection.
//!
//! Handles player-wall collisions for proper maze navigation.
//! Uses AABB (axis-aligned bounding box) collision with sliding response.
//!
//! Supports two collision backends:
//! - Legacy: `GeometryDef` array from Rhai scripts
//! - Modern: `CollisionWorld` from glTF/procedural levels (uses parry3d)

use glam::Vec3;

use crate::level::mesh::CollisionWorld;
use crate::level::segment::GeometryDef;

/// Player collision capsule (simplified as cylinder).
pub const PLAYER_RADIUS: f32 = 0.5;
pub const PLAYER_HEIGHT: f32 = 1.8;

/// Check if a point is inside an AABB (axis-aligned bounding box).
#[inline]
#[allow(dead_code)]
fn point_in_aabb(point: Vec3, center: Vec3, half_size: Vec3) -> bool {
    let min = center - half_size;
    let max = center + half_size;
    point.x >= min.x
        && point.x <= max.x
        && point.y >= min.y
        && point.y <= max.y
        && point.z >= min.z
        && point.z <= max.z
}

/// Check collision between a cylinder (player) and an AABB (wall).
/// Returns the penetration vector if colliding, None otherwise.
fn cylinder_aabb_collision(
    cylinder_pos: Vec3,
    cylinder_radius: f32,
    cylinder_height: f32,
    box_center: Vec3,
    box_half_size: Vec3,
) -> Option<Vec3> {
    // Expand the box by the cylinder radius for the XZ check
    let expanded_half = Vec3::new(
        box_half_size.x + cylinder_radius,
        box_half_size.y,
        box_half_size.z + cylinder_radius,
    );

    // Check Y overlap first (vertical)
    let player_bottom = cylinder_pos.y;
    let player_top = cylinder_pos.y + cylinder_height;
    let box_bottom = box_center.y - box_half_size.y;
    let box_top = box_center.y + box_half_size.y;

    if player_top < box_bottom || player_bottom > box_top {
        return None; // No vertical overlap
    }

    // Find closest point on expanded box to cylinder center (XZ plane)
    let closest_x = cylinder_pos
        .x
        .clamp(box_center.x - expanded_half.x, box_center.x + expanded_half.x);
    let closest_z = cylinder_pos
        .z
        .clamp(box_center.z - expanded_half.z, box_center.z + expanded_half.z);

    // Check if cylinder center is inside the expanded box (XZ)
    let _dx = cylinder_pos.x - closest_x;
    let _dz = cylinder_pos.z - closest_z;

    // If we're inside the box bounds (considering radius), we're colliding
    let in_x = cylinder_pos.x >= box_center.x - expanded_half.x
        && cylinder_pos.x <= box_center.x + expanded_half.x;
    let in_z = cylinder_pos.z >= box_center.z - expanded_half.z
        && cylinder_pos.z <= box_center.z + expanded_half.z;

    if in_x && in_z {
        // Inside the box - find the shortest push-out direction
        let to_left = cylinder_pos.x - (box_center.x - expanded_half.x);
        let to_right = (box_center.x + expanded_half.x) - cylinder_pos.x;
        let to_back = cylinder_pos.z - (box_center.z - expanded_half.z);
        let to_front = (box_center.z + expanded_half.z) - cylinder_pos.z;

        let min_dist = to_left.min(to_right).min(to_back).min(to_front);

        if min_dist == to_left {
            return Some(Vec3::new(-to_left, 0.0, 0.0));
        } else if min_dist == to_right {
            return Some(Vec3::new(to_right, 0.0, 0.0));
        } else if min_dist == to_back {
            return Some(Vec3::new(0.0, 0.0, -to_back));
        } else {
            return Some(Vec3::new(0.0, 0.0, to_front));
        }
    }

    None
}

/// Resolve collision between player position and level geometry.
/// Returns the corrected position after sliding along walls.
pub fn resolve_collisions(
    position: Vec3,
    geometry: &[GeometryDef],
    player_radius: f32,
    player_height: f32,
) -> Vec3 {
    let mut resolved = position;

    // Check against all solid geometry
    for geo in geometry.iter().filter(|g| g.solid && g.geo_type == "box") {
        let half_size = geo.size * 0.5;

        if let Some(penetration) =
            cylinder_aabb_collision(resolved, player_radius, player_height, geo.position, half_size)
        {
            // Push player out of the wall
            resolved += penetration;
        }
    }

    resolved
}

/// Check if a position is valid (not inside any solid geometry).
pub fn is_position_valid(position: Vec3, geometry: &[GeometryDef], player_radius: f32) -> bool {
    for geo in geometry.iter().filter(|g| g.solid && g.geo_type == "box") {
        let half_size = geo.size * 0.5;
        let expanded_half = half_size + Vec3::new(player_radius, 0.0, player_radius);

        // Simple AABB check with expanded bounds
        let min = geo.position - expanded_half;
        let max = geo.position + expanded_half;

        if position.x >= min.x
            && position.x <= max.x
            && position.z >= min.z
            && position.z <= max.z
            && position.y >= min.y
            && position.y <= max.y + 1.8
        {
            return false;
        }
    }
    true
}

/// Simple raycast against level geometry.
/// Returns distance to first hit, or None if no hit within max_dist.
pub fn raycast(
    origin: Vec3,
    direction: Vec3,
    geometry: &[GeometryDef],
    max_dist: f32,
) -> Option<f32> {
    let mut closest: Option<f32> = None;
    let dir = direction.normalize_or_zero();

    for geo in geometry.iter().filter(|g| g.solid && g.geo_type == "box") {
        let half_size = geo.size * 0.5;
        let min = geo.position - half_size;
        let max = geo.position + half_size;

        // Ray-AABB intersection (slab method)
        let inv_dir = Vec3::new(
            if dir.x.abs() > 1e-6 { 1.0 / dir.x } else { f32::MAX },
            if dir.y.abs() > 1e-6 { 1.0 / dir.y } else { f32::MAX },
            if dir.z.abs() > 1e-6 { 1.0 / dir.z } else { f32::MAX },
        );

        let t1 = (min.x - origin.x) * inv_dir.x;
        let t2 = (max.x - origin.x) * inv_dir.x;
        let t3 = (min.y - origin.y) * inv_dir.y;
        let t4 = (max.y - origin.y) * inv_dir.y;
        let t5 = (min.z - origin.z) * inv_dir.z;
        let t6 = (max.z - origin.z) * inv_dir.z;

        let tmin = t1.min(t2).max(t3.min(t4)).max(t5.min(t6));
        let tmax = t1.max(t2).min(t3.max(t4)).min(t5.max(t6));

        if tmax >= 0.0 && tmin <= tmax && tmin <= max_dist {
            let t = if tmin >= 0.0 { tmin } else { tmax };
            if t >= 0.0 && t <= max_dist {
                closest = Some(closest.map_or(t, |c| c.min(t)));
            }
        }
    }

    closest
}

// ============================================================================
// Modern CollisionWorld API (parry3d-based)
// ============================================================================

/// Resolve collision using the modern CollisionWorld (parry3d).
/// Returns the corrected position after sliding along surfaces.
pub fn resolve_collisions_world(
    position: Vec3,
    collision_world: &CollisionWorld,
    player_radius: f32,
    player_height: f32,
) -> Vec3 {
    collision_world.resolve_capsule_collision(position, player_radius, player_height)
}

/// Raycast using the modern CollisionWorld (parry3d).
/// Returns distance to first hit, or None if no hit within max_dist.
pub fn raycast_world(
    origin: Vec3,
    direction: Vec3,
    collision_world: &CollisionWorld,
    max_dist: f32,
) -> Option<f32> {
    collision_world.raycast(origin, direction, max_dist)
}

/// Check if a position is inside any collision geometry.
pub fn is_position_blocked(position: Vec3, collision_world: &CollisionWorld) -> bool {
    collision_world.point_inside(position)
}

/// Unified collision resolver that works with either backend.
pub enum CollisionBackend<'a> {
    /// Legacy Rhai-based geometry definitions.
    Legacy(&'a [GeometryDef]),
    /// Modern parry3d-based collision world.
    Modern(&'a CollisionWorld),
}

impl CollisionBackend<'_> {
    /// Resolve player collision and return corrected position.
    pub fn resolve_collision(&self, position: Vec3, radius: f32, height: f32) -> Vec3 {
        match self {
            Self::Legacy(geometry) => resolve_collisions(position, geometry, radius, height),
            Self::Modern(world) => resolve_collisions_world(position, world, radius, height),
        }
    }

    /// Cast a ray and return distance to first hit.
    pub fn raycast(&self, origin: Vec3, direction: Vec3, max_dist: f32) -> Option<f32> {
        match self {
            Self::Legacy(geometry) => raycast(origin, direction, geometry, max_dist),
            Self::Modern(world) => raycast_world(origin, direction, world, max_dist),
        }
    }

    /// Trace a capsule/cylinder from start to end position.
    /// Returns (fraction, end_pos, normal) where:
    /// - fraction: 0.0-1.0 how far we got (1.0 = no hit)
    /// - end_pos: final position
    /// - normal: surface normal at hit point (if any)
    pub fn trace_capsule(
        &self,
        start: Vec3,
        end: Vec3,
        radius: f32,
        height: f32,
    ) -> (f32, Vec3, Option<Vec3>) {
        match self {
            Self::Legacy(geometry) => trace_capsule_legacy(start, end, radius, height, geometry),
            Self::Modern(world) => trace_capsule_modern(start, end, radius, height, world),
        }
    }

    /// Check if a position is valid (not inside solid geometry).
    pub fn is_position_valid(&self, position: Vec3, radius: f32) -> bool {
        match self {
            Self::Legacy(geometry) => is_position_valid(position, geometry, radius),
            Self::Modern(world) => !world.point_inside(position),
        }
    }
}

/// Trace a capsule through legacy geometry.
fn trace_capsule_legacy(
    start: Vec3,
    end: Vec3,
    radius: f32,
    height: f32,
    geometry: &[GeometryDef],
) -> (f32, Vec3, Option<Vec3>) {
    let delta = end - start;
    let dist = delta.length();

    if dist < 0.0001 {
        return (1.0, start, None);
    }

    // Binary search for collision point
    let mut lo = 0.0_f32;
    let mut hi = 1.0_f32;

    // First check if end position is valid
    let end_resolved = resolve_collisions(end, geometry, radius, height);
    if (end_resolved - end).length_squared() < 0.0001 {
        // End position is clear, full move succeeded
        return (1.0, end, None);
    }

    // Binary search to find collision point
    for _ in 0..10 {
        let mid = (lo + hi) * 0.5;
        let test_pos = start + delta * mid;
        let resolved = resolve_collisions(test_pos, geometry, radius, height);

        if (resolved - test_pos).length_squared() < 0.0001 {
            // Position is clear, we can go at least this far
            lo = mid;
        } else {
            // Position is blocked
            hi = mid;
        }
    }

    let fraction = lo;
    let end_pos = start + delta * fraction;

    // Calculate approximate normal from push direction
    let test_pos = start + delta * hi;
    let resolved = resolve_collisions(test_pos, geometry, radius, height);
    let push = resolved - test_pos;

    let normal = if push.length_squared() > 0.0001 {
        push.normalize()
    } else {
        // Default to vertical push for ground
        Vec3::Y
    };

    (fraction, end_pos, Some(normal))
}

/// Trace a capsule through modern collision world.
fn trace_capsule_modern(
    start: Vec3,
    end: Vec3,
    radius: f32,
    height: f32,
    world: &CollisionWorld,
) -> (f32, Vec3, Option<Vec3>) {
    let delta = end - start;
    let dist = delta.length();

    if dist < 0.0001 {
        return (1.0, start, None);
    }

    // Binary search for collision point
    let mut lo = 0.0_f32;
    let mut hi = 1.0_f32;

    // First check if end position is valid
    let end_resolved = world.resolve_capsule_collision(end, radius, height);
    if (end_resolved - end).length_squared() < 0.0001 {
        // End position is clear, full move succeeded
        return (1.0, end, None);
    }

    // Binary search to find collision point
    for _ in 0..10 {
        let mid = (lo + hi) * 0.5;
        let test_pos = start + delta * mid;
        let resolved = world.resolve_capsule_collision(test_pos, radius, height);

        if (resolved - test_pos).length_squared() < 0.0001 {
            // Position is clear, we can go at least this far
            lo = mid;
        } else {
            // Position is blocked
            hi = mid;
        }
    }

    let fraction = lo;
    let end_pos = start + delta * fraction;

    // Calculate approximate normal from push direction
    let test_pos = start + delta * hi;
    let resolved = world.resolve_capsule_collision(test_pos, radius, height);
    let push = resolved - test_pos;

    let normal = if push.length_squared() > 0.0001 {
        push.normalize()
    } else {
        // Default to vertical push for ground
        Vec3::Y
    };

    (fraction, end_pos, Some(normal))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_wall(x: f32, y: f32, z: f32, w: f32, h: f32, d: f32) -> GeometryDef {
        GeometryDef {
            geo_type: "box".to_string(),
            position: Vec3::new(x, y, z),
            size: Vec3::new(w, h, d),
            color: [100, 100, 100],
            solid: true,
            tag: None,
        }
    }

    #[test]
    fn test_no_collision() {
        let walls = vec![make_wall(10.0, 0.0, 0.0, 2.0, 3.0, 2.0)];

        let pos = Vec3::new(0.0, 0.0, 0.0);
        let resolved = resolve_collisions(pos, &walls, PLAYER_RADIUS, PLAYER_HEIGHT);
        assert_eq!(resolved, pos);
    }

    #[test]
    fn test_wall_push_out() {
        let walls = vec![make_wall(0.0, 1.5, 0.0, 4.0, 3.0, 4.0)];

        // Player inside the wall
        let pos = Vec3::new(0.0, 0.0, 0.0);
        let resolved = resolve_collisions(pos, &walls, PLAYER_RADIUS, PLAYER_HEIGHT);

        // Should be pushed out
        assert!(
            (resolved - pos).length() > 0.1,
            "Player should be pushed out"
        );
    }

    #[test]
    fn test_raycast_hit() {
        let walls = vec![make_wall(10.0, 1.0, 0.0, 2.0, 4.0, 4.0)];

        let origin = Vec3::new(0.0, 1.0, 0.0);
        let direction = Vec3::new(1.0, 0.0, 0.0);

        let hit = raycast(origin, direction, &walls, 100.0);
        assert!(hit.is_some());
        assert!((hit.unwrap() - 9.0).abs() < 0.1); // Should hit at x=9 (wall starts at 9)
    }

    #[test]
    fn test_raycast_miss() {
        let walls = vec![make_wall(10.0, 1.0, 0.0, 2.0, 4.0, 4.0)];

        let origin = Vec3::new(0.0, 1.0, 0.0);
        let direction = Vec3::new(-1.0, 0.0, 0.0); // Opposite direction

        let hit = raycast(origin, direction, &walls, 100.0);
        assert!(hit.is_none());
    }

    // ========================================================================
    // CollisionWorld (parry3d) tests
    // ========================================================================

    #[test]
    fn test_collision_world_no_collision() {
        let mut world = CollisionWorld::new();
        world.add_box("wall", Vec3::new(10.0, 1.5, 0.0), Vec3::new(1.0, 1.5, 1.0));

        let pos = Vec3::new(0.0, 0.0, 0.0);
        let resolved = resolve_collisions_world(pos, &world, PLAYER_RADIUS, PLAYER_HEIGHT);
        assert_eq!(resolved, pos);
    }

    #[test]
    fn test_collision_world_raycast_hit() {
        let mut world = CollisionWorld::new();
        world.add_box("wall", Vec3::new(10.0, 1.0, 0.0), Vec3::new(1.0, 2.0, 2.0));

        let origin = Vec3::new(0.0, 1.0, 0.0);
        let direction = Vec3::new(1.0, 0.0, 0.0);

        let hit = raycast_world(origin, direction, &world, 100.0);
        assert!(hit.is_some());
        assert!((hit.unwrap() - 9.0).abs() < 0.1); // Should hit at x=9
    }

    #[test]
    fn test_collision_backend_legacy() {
        let walls = vec![make_wall(10.0, 1.0, 0.0, 2.0, 4.0, 4.0)];
        let backend = CollisionBackend::Legacy(&walls);

        let origin = Vec3::new(0.0, 1.0, 0.0);
        let hit = backend.raycast(origin, Vec3::X, 100.0);
        assert!(hit.is_some());
    }

    #[test]
    fn test_collision_backend_modern() {
        let mut world = CollisionWorld::new();
        world.add_box("wall", Vec3::new(10.0, 1.0, 0.0), Vec3::new(1.0, 2.0, 2.0));
        let backend = CollisionBackend::Modern(&world);

        let origin = Vec3::new(0.0, 1.0, 0.0);
        let hit = backend.raycast(origin, Vec3::X, 100.0);
        assert!(hit.is_some());
    }
}
