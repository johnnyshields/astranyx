//! Procedural mesh generators for game entities.
//!
//! All meshes oriented with X = forward (nose points +X).
//! Coordinate system: X = forward/back, Y = up/down, Z = depth/side.

use glam::Vec3;

use super::mesh::{MeshBuilder, MeshData};

/// Create a player ship mesh (fighter jet style).
pub fn create_player_ship_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();

    // Fighter jet proportions
    let nose = Vec3::new(0.5, 0.0, 0.0);

    // Cockpit area (raised canopy)
    let canopy_front = Vec3::new(0.15, 0.12, 0.0);
    let canopy_peak = Vec3::new(-0.05, 0.18, 0.0);
    let canopy_back = Vec3::new(-0.2, 0.1, 0.0);
    let canopy_l = Vec3::new(-0.05, 0.1, 0.08);
    let canopy_r = Vec3::new(-0.05, 0.1, -0.08);

    // Main fuselage (sleek body)
    let body_front_l = Vec3::new(0.1, 0.0, 0.1);
    let body_front_r = Vec3::new(0.1, 0.0, -0.1);
    let body_mid_l = Vec3::new(-0.15, 0.0, 0.12);
    let body_mid_r = Vec3::new(-0.15, 0.0, -0.12);
    let body_back_l = Vec3::new(-0.4, 0.0, 0.08);
    let body_back_r = Vec3::new(-0.4, 0.0, -0.08);

    // Underside
    let belly_front = Vec3::new(0.1, -0.06, 0.0);
    let belly_mid = Vec3::new(-0.15, -0.08, 0.0);
    let belly_back = Vec3::new(-0.4, -0.05, 0.0);

    // Tail
    let tail_top = Vec3::new(-0.5, 0.15, 0.0);
    let tail_bot = Vec3::new(-0.5, -0.03, 0.0);
    let tail_l = Vec3::new(-0.5, 0.0, 0.05);
    let tail_r = Vec3::new(-0.5, 0.0, -0.05);

    // === NOSE CONE ===
    // Top nose surfaces
    builder.add_triangle(nose, canopy_front, body_front_l);
    builder.add_triangle(nose, body_front_r, canopy_front);
    // Bottom nose surfaces
    builder.add_triangle(nose, body_front_l, belly_front);
    builder.add_triangle(nose, belly_front, body_front_r);

    // === CANOPY (raised cockpit) ===
    builder.add_triangle(canopy_front, canopy_peak, canopy_l);
    builder.add_triangle(canopy_front, canopy_r, canopy_peak);
    builder.add_triangle(canopy_peak, canopy_back, canopy_l);
    builder.add_triangle(canopy_peak, canopy_r, canopy_back);

    // === MAIN BODY TOP ===
    // Front to mid
    builder.add_triangle(canopy_front, canopy_l, body_front_l);
    builder.add_triangle(canopy_front, body_front_r, canopy_r);
    builder.add_triangle(canopy_l, body_mid_l, body_front_l);
    builder.add_triangle(canopy_r, body_front_r, body_mid_r);
    // Mid to back
    builder.add_triangle(canopy_back, body_back_l, body_mid_l);
    builder.add_triangle(canopy_back, body_mid_l, canopy_l);
    builder.add_triangle(canopy_back, body_mid_r, body_back_r);
    builder.add_triangle(canopy_back, canopy_r, body_mid_r);

    // === UNDERSIDE ===
    builder.add_triangle(body_front_l, belly_mid, belly_front);
    builder.add_triangle(body_front_l, body_mid_l, belly_mid);
    builder.add_triangle(body_front_r, belly_front, belly_mid);
    builder.add_triangle(body_front_r, belly_mid, body_mid_r);
    builder.add_triangle(body_mid_l, belly_back, belly_mid);
    builder.add_triangle(body_mid_l, body_back_l, belly_back);
    builder.add_triangle(body_mid_r, belly_mid, belly_back);
    builder.add_triangle(body_mid_r, belly_back, body_back_r);

    // === TAIL SECTION ===
    // Top to tail
    builder.add_triangle(canopy_back, tail_top, body_back_l);
    builder.add_triangle(canopy_back, body_back_r, tail_top);
    // Sides to tail
    builder.add_triangle(body_back_l, tail_top, tail_l);
    builder.add_triangle(body_back_r, tail_r, tail_top);
    // Bottom to tail
    builder.add_triangle(body_back_l, tail_l, belly_back);
    builder.add_triangle(body_back_r, belly_back, tail_r);
    builder.add_triangle(belly_back, tail_l, tail_bot);
    builder.add_triangle(belly_back, tail_bot, tail_r);
    // Tail back face
    builder.add_triangle(tail_top, tail_r, tail_l);
    builder.add_triangle(tail_bot, tail_l, tail_r);

    // === SWEPT WINGS ===
    let wing_root = Vec3::new(-0.1, -0.02, 0.12);
    let wing_tip = Vec3::new(-0.3, -0.02, 0.4);
    let wing_back = Vec3::new(-0.35, -0.02, 0.1);
    // Left wing top
    builder.add_triangle(
        wing_root + Vec3::Y * 0.02,
        wing_tip + Vec3::Y * 0.01,
        wing_back + Vec3::Y * 0.02,
    );
    // Left wing bottom
    builder.add_triangle(wing_root, wing_back, wing_tip);

    // Right wing (mirror)
    let wing_root_r = Vec3::new(-0.1, -0.02, -0.12);
    let wing_tip_r = Vec3::new(-0.3, -0.02, -0.4);
    let wing_back_r = Vec3::new(-0.35, -0.02, -0.1);
    // Right wing top
    builder.add_triangle(
        wing_root_r + Vec3::Y * 0.02,
        wing_back_r + Vec3::Y * 0.02,
        wing_tip_r + Vec3::Y * 0.01,
    );
    // Right wing bottom
    builder.add_triangle(wing_root_r, wing_tip_r, wing_back_r);

    // === VERTICAL TAIL FIN ===
    let fin_base1 = Vec3::new(-0.35, 0.05, 0.0);
    let fin_base2 = Vec3::new(-0.5, 0.05, 0.0);
    let fin_tip = Vec3::new(-0.48, 0.28, 0.0);
    // Both sides of fin
    builder.add_triangle(fin_base1, fin_tip, fin_base2);
    builder.add_triangle(fin_base1, fin_base2, fin_tip);

    builder.finish()
}

/// Create an enemy ship mesh (angular, menacing).
pub fn create_enemy_ship_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();

    // Enemy faces left (negative X direction)
    let nose = Vec3::new(-0.5, 0.0, 0.0);
    let top_front = Vec3::new(0.2, 0.0, 0.3);
    let top_back = Vec3::new(0.5, 0.0, 0.2);
    let bot_front = Vec3::new(0.2, 0.0, -0.3);
    let bot_back = Vec3::new(0.5, 0.0, -0.2);
    let wing_top_l = Vec3::new(0.3, 0.5, 0.1);
    let wing_top_r = Vec3::new(0.3, -0.5, 0.1);
    let wing_bot_l = Vec3::new(0.3, 0.5, -0.1);
    let wing_bot_r = Vec3::new(0.3, -0.5, -0.1);

    // Top hull
    builder.add_triangle(nose, top_front, wing_top_l);
    builder.add_triangle(nose, wing_top_r, top_front);
    builder.add_triangle(top_front, top_back, wing_top_l);
    builder.add_triangle(top_front, wing_top_r, top_back);

    // Bottom hull
    builder.add_triangle(nose, wing_bot_l, bot_front);
    builder.add_triangle(nose, bot_front, wing_bot_r);
    builder.add_triangle(bot_front, wing_bot_l, bot_back);
    builder.add_triangle(bot_front, bot_back, wing_bot_r);

    // Sides
    builder.add_triangle(nose, top_front, bot_front);
    builder.add_triangle(top_front, top_back, bot_back);
    builder.add_triangle(top_front, bot_back, bot_front);

    // Back
    builder.add_triangle(top_back, bot_back, wing_bot_l);
    builder.add_triangle(top_back, wing_bot_l, wing_top_l);
    builder.add_triangle(top_back, wing_top_r, wing_bot_r);
    builder.add_triangle(top_back, wing_bot_r, bot_back);

    builder.finish()
}

/// Create a tank enemy mesh (boxy, armored).
pub fn create_tank_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();

    // Main body
    builder.add_box(0.8, 0.6, 0.8);

    // Turret on top (offset up)
    let tw = 0.2;
    let th = 0.15;
    let td = 0.2;
    let ty = 0.3 + th;

    // Turret faces
    let turret_offset = Vec3::new(0.0, ty - th, 0.0);

    // Turret front
    builder.add_triangle(
        Vec3::new(-tw, ty - th * 2.0, td) + turret_offset,
        Vec3::new(tw, ty - th * 2.0, td) + turret_offset,
        Vec3::new(tw, ty, td) + turret_offset,
    );
    builder.add_triangle(
        Vec3::new(-tw, ty - th * 2.0, td) + turret_offset,
        Vec3::new(tw, ty, td) + turret_offset,
        Vec3::new(-tw, ty, td) + turret_offset,
    );

    builder.finish()
}

/// Create a boss core mesh (octahedron).
pub fn create_boss_core_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();
    builder.add_octahedron(0.5);
    builder.finish()
}

/// Create a drone mesh (small octahedron).
pub fn create_drone_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();
    builder.add_octahedron(0.4);
    builder.finish()
}

/// Create a powerup mesh (diamond shape).
pub fn create_powerup_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();
    builder.add_pyramid(0.4, 0.5);
    builder.finish()
}

/// Create a mine mesh (spiky sphere).
pub fn create_mine_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();

    let r = 0.3;
    let spike_r = 0.5;
    let spike_w = 0.1;

    let dirs: [[f32; 3]; 6] = [
        [1.0, 0.0, 0.0],
        [-1.0, 0.0, 0.0],
        [0.0, 1.0, 0.0],
        [0.0, -1.0, 0.0],
        [0.0, 0.0, 1.0],
        [0.0, 0.0, -1.0],
    ];

    for dir in &dirs {
        let d = Vec3::from_array(*dir);
        let tip = d * spike_r;
        let base = d * r;

        // Find perpendicular vectors
        let (perp1, perp2) = if dir[0].abs() > 0.9 {
            (Vec3::new(0.0, spike_w, 0.0), Vec3::new(0.0, 0.0, spike_w))
        } else if dir[1].abs() > 0.9 {
            (Vec3::new(spike_w, 0.0, 0.0), Vec3::new(0.0, 0.0, spike_w))
        } else {
            (Vec3::new(spike_w, 0.0, 0.0), Vec3::new(0.0, spike_w, 0.0))
        };

        let b1 = base + perp1;
        let b2 = base + perp2;
        let b3 = base - perp1;
        let b4 = base - perp2;

        builder.add_triangle(tip, b1, b2);
        builder.add_triangle(tip, b2, b3);
        builder.add_triangle(tip, b3, b4);
        builder.add_triangle(tip, b4, b1);
    }

    builder.finish()
}

/// Create a simple bullet mesh (elongated octahedron).
pub fn create_bullet_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();

    // Elongated along X axis
    let front = Vec3::new(0.15, 0.0, 0.0);
    let back = Vec3::new(-0.05, 0.0, 0.0);
    let r = 0.03;

    let corners = [
        Vec3::new(0.0, r, 0.0),
        Vec3::new(0.0, 0.0, r),
        Vec3::new(0.0, -r, 0.0),
        Vec3::new(0.0, 0.0, -r),
    ];

    for i in 0..4 {
        let c1 = corners[i];
        let c2 = corners[(i + 1) % 4];
        builder.add_triangle(front, c1, c2);
        builder.add_triangle(back, c2, c1);
    }

    builder.finish()
}

/// Create a laser beam mesh (thin cylinder).
pub fn create_laser_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();
    builder.add_cylinder(0.02, 0.5, 6);
    builder.finish()
}

/// Create an icosahedron (orb) mesh.
pub fn create_orb_mesh() -> MeshData {
    let mut builder = MeshBuilder::new();

    let t = (1.0 + 5.0_f32.sqrt()) / 2.0;
    let r = 0.3;

    let verts: Vec<Vec3> = [
        [-1.0, t, 0.0],
        [1.0, t, 0.0],
        [-1.0, -t, 0.0],
        [1.0, -t, 0.0],
        [0.0, -1.0, t],
        [0.0, 1.0, t],
        [0.0, -1.0, -t],
        [0.0, 1.0, -t],
        [t, 0.0, -1.0],
        [t, 0.0, 1.0],
        [-t, 0.0, -1.0],
        [-t, 0.0, 1.0],
    ]
    .iter()
    .map(|v| Vec3::new(v[0], v[1], v[2]).normalize() * r)
    .collect();

    let faces: [[usize; 3]; 20] = [
        [0, 11, 5],
        [0, 5, 1],
        [0, 1, 7],
        [0, 7, 10],
        [0, 10, 11],
        [1, 5, 9],
        [5, 11, 4],
        [11, 10, 2],
        [10, 7, 6],
        [7, 1, 8],
        [3, 9, 4],
        [3, 4, 2],
        [3, 2, 6],
        [3, 6, 8],
        [3, 8, 9],
        [4, 9, 5],
        [2, 4, 11],
        [6, 2, 10],
        [8, 6, 7],
        [9, 8, 1],
    ];

    for face in &faces {
        builder.add_triangle(verts[face[0]], verts[face[1]], verts[face[2]]);
    }

    builder.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_player_ship_mesh() {
        let mesh = create_player_ship_mesh();
        assert!(mesh.vertex_count() > 0);
        // Should have many triangles for a detailed ship
        assert!(mesh.vertex_count() >= 90); // At least 30 triangles
    }

    #[test]
    fn test_enemy_ship_mesh() {
        let mesh = create_enemy_ship_mesh();
        assert!(mesh.vertex_count() > 0);
    }

    #[test]
    fn test_bullet_mesh() {
        let mesh = create_bullet_mesh();
        assert_eq!(mesh.vertex_count(), 24); // 8 triangles * 3 vertices
    }

    #[test]
    fn test_orb_mesh() {
        let mesh = create_orb_mesh();
        assert_eq!(mesh.vertex_count(), 60); // 20 faces * 3 vertices
    }
}
