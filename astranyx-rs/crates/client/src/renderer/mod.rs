//! Three-d based renderer for Astranyx.
//!
//! Uses the three-d crate for simple 3D rendering.

use std::collections::HashMap;

use glam::{Vec3, Vec4};
use three_d::*;

/// Simple mesh data for registration.
pub struct MeshData {
    pub positions: Vec<Vec3>,
    pub normals: Vec<Vec3>,
    pub indices: Vec<u32>,
}

/// Builder for creating mesh data.
pub struct MeshBuilder {
    positions: Vec<Vec3>,
    normals: Vec<Vec3>,
    indices: Vec<u32>,
}

impl MeshBuilder {
    pub fn new() -> Self {
        Self {
            positions: Vec::new(),
            normals: Vec::new(),
            indices: Vec::new(),
        }
    }

    /// Add a box centered at origin with given dimensions.
    pub fn add_box(&mut self, width: f32, height: f32, depth: f32) {
        let hw = width / 2.0;
        let hh = height / 2.0;
        let hd = depth / 2.0;

        let base = self.positions.len() as u32;

        // Front face
        self.positions.extend([
            Vec3::new(-hw, -hh, hd),
            Vec3::new(hw, -hh, hd),
            Vec3::new(hw, hh, hd),
            Vec3::new(-hw, hh, hd),
        ]);
        self.normals.extend([Vec3::Z; 4]);
        self.indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

        // Back face
        let base = self.positions.len() as u32;
        self.positions.extend([
            Vec3::new(hw, -hh, -hd),
            Vec3::new(-hw, -hh, -hd),
            Vec3::new(-hw, hh, -hd),
            Vec3::new(hw, hh, -hd),
        ]);
        self.normals.extend([Vec3::NEG_Z; 4]);
        self.indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

        // Top face
        let base = self.positions.len() as u32;
        self.positions.extend([
            Vec3::new(-hw, hh, hd),
            Vec3::new(hw, hh, hd),
            Vec3::new(hw, hh, -hd),
            Vec3::new(-hw, hh, -hd),
        ]);
        self.normals.extend([Vec3::Y; 4]);
        self.indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

        // Bottom face
        let base = self.positions.len() as u32;
        self.positions.extend([
            Vec3::new(-hw, -hh, -hd),
            Vec3::new(hw, -hh, -hd),
            Vec3::new(hw, -hh, hd),
            Vec3::new(-hw, -hh, hd),
        ]);
        self.normals.extend([Vec3::NEG_Y; 4]);
        self.indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

        // Right face
        let base = self.positions.len() as u32;
        self.positions.extend([
            Vec3::new(hw, -hh, hd),
            Vec3::new(hw, -hh, -hd),
            Vec3::new(hw, hh, -hd),
            Vec3::new(hw, hh, hd),
        ]);
        self.normals.extend([Vec3::X; 4]);
        self.indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

        // Left face
        let base = self.positions.len() as u32;
        self.positions.extend([
            Vec3::new(-hw, -hh, -hd),
            Vec3::new(-hw, -hh, hd),
            Vec3::new(-hw, hh, hd),
            Vec3::new(-hw, hh, -hd),
        ]);
        self.normals.extend([Vec3::NEG_X; 4]);
        self.indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);
    }

    /// Add a diamond/octahedron shape.
    pub fn add_diamond(&mut self, size: f32) {
        let base = self.positions.len() as u32;
        let h = size;
        let w = size * 0.5;

        // 6 vertices: top, bottom, and 4 around middle
        self.positions.extend([
            Vec3::new(0.0, h, 0.0),     // 0: top
            Vec3::new(0.0, -h, 0.0),    // 1: bottom
            Vec3::new(w, 0.0, 0.0),     // 2: right
            Vec3::new(-w, 0.0, 0.0),    // 3: left
            Vec3::new(0.0, 0.0, w),     // 4: front
            Vec3::new(0.0, 0.0, -w),    // 5: back
        ]);

        // Normals (approximate)
        self.normals.extend([
            Vec3::Y,
            Vec3::NEG_Y,
            Vec3::X,
            Vec3::NEG_X,
            Vec3::Z,
            Vec3::NEG_Z,
        ]);

        // 8 triangular faces
        self.indices.extend([
            // Top faces
            base, base + 4, base + 2, // top-front-right
            base, base + 2, base + 5, // top-right-back
            base, base + 5, base + 3, // top-back-left
            base, base + 3, base + 4, // top-left-front
            // Bottom faces
            base + 1, base + 2, base + 4, // bottom-right-front
            base + 1, base + 5, base + 2, // bottom-back-right
            base + 1, base + 3, base + 5, // bottom-left-back
            base + 1, base + 4, base + 3, // bottom-front-left
        ]);
    }

    /// Add a cone/wedge shape pointing right (for ships).
    pub fn add_ship_cone(&mut self, length: f32, width: f32, height: f32) {
        let base = self.positions.len() as u32;

        // Ship points right (+X), centered at origin
        let tip = Vec3::new(length / 2.0, 0.0, 0.0);
        let back_top = Vec3::new(-length / 2.0, height / 2.0, 0.0);
        let back_bottom = Vec3::new(-length / 2.0, -height / 2.0, 0.0);
        let back_left = Vec3::new(-length / 2.0, 0.0, -width / 2.0);
        let back_right = Vec3::new(-length / 2.0, 0.0, width / 2.0);

        self.positions.extend([tip, back_top, back_bottom, back_left, back_right]);

        // Simple normals
        self.normals.extend([
            Vec3::X,
            Vec3::new(-0.5, 0.5, 0.0).normalize(),
            Vec3::new(-0.5, -0.5, 0.0).normalize(),
            Vec3::new(-0.5, 0.0, -0.5).normalize(),
            Vec3::new(-0.5, 0.0, 0.5).normalize(),
        ]);

        // 4 triangular faces + 2 back faces
        self.indices.extend([
            base, base + 4, base + 1, // top-right
            base, base + 1, base + 3, // top-left
            base, base + 3, base + 2, // bottom-left
            base, base + 2, base + 4, // bottom-right
            // Back face (two triangles)
            base + 1, base + 4, base + 2,
            base + 1, base + 2, base + 3,
        ]);
    }

    pub fn finish(self) -> MeshData {
        MeshData {
            positions: self.positions,
            normals: self.normals,
            indices: self.indices,
        }
    }
}

impl Default for MeshBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Pre-built mesh generators.
pub mod meshes {
    use super::*;

    pub fn create_player_ship_mesh() -> MeshData {
        let mut builder = MeshBuilder::new();
        builder.add_ship_cone(1.0, 0.4, 0.3);
        builder.finish()
    }

    pub fn create_enemy_ship_mesh() -> MeshData {
        let mut builder = MeshBuilder::new();
        builder.add_box(0.8, 0.5, 0.4);
        builder.finish()
    }

    pub fn create_drone_mesh() -> MeshData {
        let mut builder = MeshBuilder::new();
        builder.add_diamond(0.5);
        builder.finish()
    }

    pub fn create_tank_mesh() -> MeshData {
        let mut builder = MeshBuilder::new();
        builder.add_box(1.0, 0.6, 0.6);
        builder.finish()
    }

    pub fn create_boss_core_mesh() -> MeshData {
        let mut builder = MeshBuilder::new();
        builder.add_box(1.5, 1.0, 0.8);
        builder.finish()
    }

    pub fn create_bullet_mesh() -> MeshData {
        let mut builder = MeshBuilder::new();
        builder.add_box(0.4, 0.15, 0.15);
        builder.finish()
    }

    pub fn create_laser_mesh() -> MeshData {
        let mut builder = MeshBuilder::new();
        builder.add_box(1.0, 0.1, 0.1);
        builder.finish()
    }

    pub fn create_powerup_mesh() -> MeshData {
        let mut builder = MeshBuilder::new();
        builder.add_diamond(0.5);
        builder.finish()
    }
}

/// A registered mesh with its GPU data.
struct RegisteredMesh {
    cpu_mesh: CpuMesh,
}

/// Instance data for batched rendering.
pub struct Instance {
    pub position: Vec3,
    pub scale: Vec3,
    pub rotation: Vec3,
    pub color: Vec4,
}

/// The main renderer using three-d.
pub struct GameRenderer {
    meshes: HashMap<String, RegisteredMesh>,
    time: f32,
}

impl GameRenderer {
    pub fn new() -> Self {
        Self {
            meshes: HashMap::new(),
            time: 0.0,
        }
    }

    /// Register a mesh by name.
    pub fn register_mesh(&mut self, name: &str, data: &MeshData) {
        let positions: Vec<three_d::Vec3> = data
            .positions
            .iter()
            .map(|p| three_d::Vec3::new(p.x, p.y, p.z))
            .collect();

        let normals: Vec<three_d::Vec3> = data
            .normals
            .iter()
            .map(|n| three_d::Vec3::new(n.x, n.y, n.z))
            .collect();

        let cpu_mesh = CpuMesh {
            positions: Positions::F32(positions),
            normals: Some(normals),
            indices: Indices::U32(data.indices.clone()),
            ..Default::default()
        };

        self.meshes.insert(name.to_string(), RegisteredMesh { cpu_mesh });
    }

    /// Get the current time.
    pub fn time(&self) -> f32 {
        self.time
    }

    /// Update time.
    pub fn update_time(&mut self, delta: f32) {
        self.time += delta;
    }

    /// Get a mesh by name for rendering.
    pub fn get_mesh(&self, name: &str) -> Option<&CpuMesh> {
        self.meshes.get(name).map(|m| &m.cpu_mesh)
    }
}

impl Default for GameRenderer {
    fn default() -> Self {
        Self::new()
    }
}

// Re-export
pub use self::meshes::*;
