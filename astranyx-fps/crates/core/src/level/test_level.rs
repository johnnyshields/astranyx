//! Procedural test level generation for FPS movement testing.
//!
//! Creates simple collision geometry for testing player movement without
//! requiring glTF or Rhai script loading.

use glam::Vec3;

use super::segment::GeometryDef;

/// Generate a simple test arena for FPS movement.
///
/// Creates:
/// - Floor plane
/// - Four outer walls
/// - A few interior obstacles for collision testing
/// - A ramp for testing slopes
/// - Steps for testing stair climbing
pub fn generate_test_arena() -> Vec<GeometryDef> {
    let mut geometry = Vec::new();

    // === FLOOR ===
    // Large floor plane (solid for ground detection)
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(0.0, -0.5, 0.0),
        size: Vec3::new(100.0, 1.0, 100.0),
        color: [80, 80, 85],
        solid: true,
        tag: Some("floor".to_string()),
    });

    // === OUTER WALLS ===
    let wall_height = 10.0;
    let wall_thickness = 1.0;
    let arena_size = 50.0;

    // North wall (-Z)
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(0.0, wall_height / 2.0, -arena_size),
        size: Vec3::new(arena_size * 2.0 + wall_thickness, wall_height, wall_thickness),
        color: [60, 55, 65],
        solid: true,
        tag: Some("wall".to_string()),
    });

    // South wall (+Z)
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(0.0, wall_height / 2.0, arena_size),
        size: Vec3::new(arena_size * 2.0 + wall_thickness, wall_height, wall_thickness),
        color: [60, 55, 65],
        solid: true,
        tag: Some("wall".to_string()),
    });

    // West wall (-X)
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(-arena_size, wall_height / 2.0, 0.0),
        size: Vec3::new(wall_thickness, wall_height, arena_size * 2.0),
        color: [55, 55, 60],
        solid: true,
        tag: Some("wall".to_string()),
    });

    // East wall (+X)
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(arena_size, wall_height / 2.0, 0.0),
        size: Vec3::new(wall_thickness, wall_height, arena_size * 2.0),
        color: [55, 55, 60],
        solid: true,
        tag: Some("wall".to_string()),
    });

    // === INTERIOR OBSTACLES ===

    // Central pillar (test sliding around corners)
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(0.0, 2.0, 0.0),
        size: Vec3::new(4.0, 4.0, 4.0),
        color: [70, 65, 75],
        solid: true,
        tag: Some("pillar".to_string()),
    });

    // Crates for cover (different heights)
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(-15.0, 1.0, 10.0),
        size: Vec3::new(3.0, 2.0, 3.0),
        color: [100, 80, 60],
        solid: true,
        tag: Some("crate".to_string()),
    });

    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(-12.0, 0.75, 10.0),
        size: Vec3::new(2.5, 1.5, 2.5),
        color: [95, 75, 55],
        solid: true,
        tag: Some("crate".to_string()),
    });

    // Low wall (test crouching under - not implemented yet but prepare for it)
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(15.0, 0.75, -10.0),
        size: Vec3::new(8.0, 1.5, 1.0),
        color: [65, 60, 70],
        solid: true,
        tag: Some("low_wall".to_string()),
    });

    // === STAIRS (test step climbing) ===
    // 4 steps, each 0.4m high (under STEP_SIZE of 0.5m)
    for i in 0..4 {
        let step_y = 0.2 + (i as f32 * 0.4);
        let step_z = -25.0 - (i as f32 * 1.0);

        geometry.push(GeometryDef {
            geo_type: "box".to_string(),
            position: Vec3::new(20.0, step_y, step_z),
            size: Vec3::new(4.0, 0.4, 1.0),
            color: [75, 70, 80],
            solid: true,
            tag: Some("stair".to_string()),
        });
    }

    // Platform at top of stairs
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(20.0, 1.8, -30.0),
        size: Vec3::new(6.0, 0.2, 4.0),
        color: [70, 65, 75],
        solid: true,
        tag: Some("platform".to_string()),
    });

    // === L-SHAPED CORRIDOR (test navigation) ===
    // First segment (along -X)
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(-30.0, 2.0, -20.0),
        size: Vec3::new(1.0, 4.0, 10.0),
        color: [65, 60, 70],
        solid: true,
        tag: Some("corridor_wall".to_string()),
    });
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(-30.0, 2.0, -30.0),
        size: Vec3::new(10.0, 4.0, 1.0),
        color: [65, 60, 70],
        solid: true,
        tag: Some("corridor_wall".to_string()),
    });

    // === RAISED PLATFORM (test jumping onto) ===
    geometry.push(GeometryDef {
        geo_type: "box".to_string(),
        position: Vec3::new(-20.0, 0.5, 30.0),
        size: Vec3::new(8.0, 1.0, 8.0),
        color: [85, 80, 90],
        solid: true,
        tag: Some("platform".to_string()),
    });

    geometry
}

/// Generate a minimal test level with just floor and one wall.
/// Useful for debugging basic movement.
pub fn generate_minimal_test() -> Vec<GeometryDef> {
    vec![
        // Floor
        GeometryDef {
            geo_type: "box".to_string(),
            position: Vec3::new(0.0, -0.5, 0.0),
            size: Vec3::new(100.0, 1.0, 100.0),
            color: [80, 80, 85],
            solid: true,
            tag: Some("floor".to_string()),
        },
        // Single wall for testing collision
        GeometryDef {
            geo_type: "box".to_string(),
            position: Vec3::new(10.0, 2.0, 0.0),
            size: Vec3::new(1.0, 4.0, 20.0),
            color: [60, 55, 65],
            solid: true,
            tag: Some("wall".to_string()),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arena_generation() {
        let geometry = generate_test_arena();

        // Should have floor + 4 walls + obstacles
        assert!(geometry.len() >= 5);

        // Floor should be at y = -0.5
        let floor = geometry.iter().find(|g| g.tag.as_deref() == Some("floor"));
        assert!(floor.is_some());
        assert_eq!(floor.unwrap().position.y, -0.5);
    }

    #[test]
    fn test_minimal_level() {
        let geometry = generate_minimal_test();
        assert_eq!(geometry.len(), 2);
    }
}
