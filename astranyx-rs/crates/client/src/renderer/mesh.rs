//! Mesh building utilities for procedural 3D geometry.
//!
//! All meshes are arrays of triangles with position + normal data.

use glam::Vec3;

/// Vertex with position and normal.
#[repr(C)]
#[derive(Copy, Clone, Debug, bytemuck::Pod, bytemuck::Zeroable)]
pub struct MeshVertex {
    pub position: [f32; 3],
    pub normal: [f32; 3],
}

impl MeshVertex {
    pub const ATTRIBS: [wgpu::VertexAttribute; 2] =
        wgpu::vertex_attr_array![0 => Float32x3, 1 => Float32x3];

    pub fn desc() -> wgpu::VertexBufferLayout<'static> {
        wgpu::VertexBufferLayout {
            array_stride: std::mem::size_of::<MeshVertex>() as wgpu::BufferAddress,
            step_mode: wgpu::VertexStepMode::Vertex,
            attributes: &Self::ATTRIBS,
        }
    }
}

/// Built mesh data ready for GPU upload.
pub struct MeshData {
    pub vertices: Vec<MeshVertex>,
}

impl MeshData {
    pub fn vertex_count(&self) -> u32 {
        self.vertices.len() as u32
    }
}

/// Fluent mesh builder for procedural geometry.
pub struct MeshBuilder {
    vertices: Vec<MeshVertex>,
}

impl Default for MeshBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl MeshBuilder {
    pub fn new() -> Self {
        Self {
            vertices: Vec::new(),
        }
    }

    /// Add a triangle with automatic normal calculation.
    pub fn add_triangle(&mut self, p1: Vec3, p2: Vec3, p3: Vec3) -> &mut Self {
        // Calculate normal from cross product of edges.
        let u = p2 - p1;
        let v = p3 - p1;
        let normal = u.cross(v).normalize_or_zero();

        self.vertices.push(MeshVertex {
            position: p1.into(),
            normal: normal.into(),
        });
        self.vertices.push(MeshVertex {
            position: p2.into(),
            normal: normal.into(),
        });
        self.vertices.push(MeshVertex {
            position: p3.into(),
            normal: normal.into(),
        });

        self
    }

    /// Add a triangle with explicit normals.
    pub fn add_triangle_with_normals(
        &mut self,
        p1: Vec3,
        n1: Vec3,
        p2: Vec3,
        n2: Vec3,
        p3: Vec3,
        n3: Vec3,
    ) -> &mut Self {
        self.vertices.push(MeshVertex {
            position: p1.into(),
            normal: n1.into(),
        });
        self.vertices.push(MeshVertex {
            position: p2.into(),
            normal: n2.into(),
        });
        self.vertices.push(MeshVertex {
            position: p3.into(),
            normal: n3.into(),
        });
        self
    }

    /// Add a quad (two triangles) with automatic normal calculation.
    pub fn add_quad(&mut self, p1: Vec3, p2: Vec3, p3: Vec3, p4: Vec3) -> &mut Self {
        // Quad vertices in order: 1, 2, 3, 4 (counter-clockwise)
        // First triangle: 1, 2, 3
        // Second triangle: 1, 3, 4
        self.add_triangle(p1, p2, p3);
        self.add_triangle(p1, p3, p4);
        self
    }

    /// Add a box centered at origin.
    pub fn add_box(&mut self, width: f32, height: f32, depth: f32) -> &mut Self {
        let hw = width / 2.0;
        let hh = height / 2.0;
        let hd = depth / 2.0;

        // Front face (Z+)
        self.add_triangle(
            Vec3::new(-hw, -hh, hd),
            Vec3::new(hw, -hh, hd),
            Vec3::new(hw, hh, hd),
        );
        self.add_triangle(
            Vec3::new(-hw, -hh, hd),
            Vec3::new(hw, hh, hd),
            Vec3::new(-hw, hh, hd),
        );

        // Back face (Z-)
        self.add_triangle(
            Vec3::new(hw, -hh, -hd),
            Vec3::new(-hw, -hh, -hd),
            Vec3::new(-hw, hh, -hd),
        );
        self.add_triangle(
            Vec3::new(hw, -hh, -hd),
            Vec3::new(-hw, hh, -hd),
            Vec3::new(hw, hh, -hd),
        );

        // Top face (Y+)
        self.add_triangle(
            Vec3::new(-hw, hh, hd),
            Vec3::new(hw, hh, hd),
            Vec3::new(hw, hh, -hd),
        );
        self.add_triangle(
            Vec3::new(-hw, hh, hd),
            Vec3::new(hw, hh, -hd),
            Vec3::new(-hw, hh, -hd),
        );

        // Bottom face (Y-)
        self.add_triangle(
            Vec3::new(-hw, -hh, -hd),
            Vec3::new(hw, -hh, -hd),
            Vec3::new(hw, -hh, hd),
        );
        self.add_triangle(
            Vec3::new(-hw, -hh, -hd),
            Vec3::new(hw, -hh, hd),
            Vec3::new(-hw, -hh, hd),
        );

        // Right face (X+)
        self.add_triangle(
            Vec3::new(hw, -hh, hd),
            Vec3::new(hw, -hh, -hd),
            Vec3::new(hw, hh, -hd),
        );
        self.add_triangle(
            Vec3::new(hw, -hh, hd),
            Vec3::new(hw, hh, -hd),
            Vec3::new(hw, hh, hd),
        );

        // Left face (X-)
        self.add_triangle(
            Vec3::new(-hw, -hh, -hd),
            Vec3::new(-hw, -hh, hd),
            Vec3::new(-hw, hh, hd),
        );
        self.add_triangle(
            Vec3::new(-hw, -hh, -hd),
            Vec3::new(-hw, hh, hd),
            Vec3::new(-hw, hh, -hd),
        );

        self
    }

    /// Add a cylinder along the X axis.
    pub fn add_cylinder(&mut self, radius: f32, length: f32, segments: u32) -> &mut Self {
        let half_len = length / 2.0;
        let segments = segments.max(3);

        for i in 0..segments {
            let a1 = (i as f32 / segments as f32) * std::f32::consts::TAU;
            let a2 = ((i + 1) as f32 / segments as f32) * std::f32::consts::TAU;
            let y1 = a1.cos() * radius;
            let z1 = a1.sin() * radius;
            let y2 = a2.cos() * radius;
            let z2 = a2.sin() * radius;

            // Side faces
            self.add_triangle(
                Vec3::new(-half_len, y1, z1),
                Vec3::new(half_len, y1, z1),
                Vec3::new(half_len, y2, z2),
            );
            self.add_triangle(
                Vec3::new(-half_len, y1, z1),
                Vec3::new(half_len, y2, z2),
                Vec3::new(-half_len, y2, z2),
            );

            // Front cap
            self.add_triangle(
                Vec3::new(half_len, 0.0, 0.0),
                Vec3::new(half_len, y1, z1),
                Vec3::new(half_len, y2, z2),
            );

            // Back cap
            self.add_triangle(
                Vec3::new(-half_len, 0.0, 0.0),
                Vec3::new(-half_len, y2, z2),
                Vec3::new(-half_len, y1, z1),
            );
        }

        self
    }

    /// Add a cone pointing along the X axis.
    pub fn add_cone(&mut self, radius: f32, length: f32, segments: u32) -> &mut Self {
        let segments = segments.max(3);

        for i in 0..segments {
            let a1 = (i as f32 / segments as f32) * std::f32::consts::TAU;
            let a2 = ((i + 1) as f32 / segments as f32) * std::f32::consts::TAU;
            let y1 = a1.cos() * radius;
            let z1 = a1.sin() * radius;
            let y2 = a2.cos() * radius;
            let z2 = a2.sin() * radius;

            // Side face
            self.add_triangle(
                Vec3::new(0.0, y1, z1),
                Vec3::new(length, 0.0, 0.0),
                Vec3::new(0.0, y2, z2),
            );

            // Base cap
            self.add_triangle(
                Vec3::new(0.0, 0.0, 0.0),
                Vec3::new(0.0, y2, z2),
                Vec3::new(0.0, y1, z1),
            );
        }

        self
    }

    /// Add an octahedron (diamond shape).
    pub fn add_octahedron(&mut self, radius: f32) -> &mut Self {
        let top = Vec3::new(0.0, 0.0, radius);
        let bot = Vec3::new(0.0, 0.0, -radius);
        let front = Vec3::new(radius, 0.0, 0.0);
        let back = Vec3::new(-radius, 0.0, 0.0);
        let left = Vec3::new(0.0, radius, 0.0);
        let right = Vec3::new(0.0, -radius, 0.0);

        // Top pyramid
        self.add_triangle(top, front, left);
        self.add_triangle(top, left, back);
        self.add_triangle(top, back, right);
        self.add_triangle(top, right, front);

        // Bottom pyramid
        self.add_triangle(bot, left, front);
        self.add_triangle(bot, back, left);
        self.add_triangle(bot, right, back);
        self.add_triangle(bot, front, right);

        self
    }

    /// Add a pyramid (double pyramid / diamond shape).
    pub fn add_pyramid(&mut self, radius: f32, height: f32) -> &mut Self {
        let top = Vec3::new(0.0, 0.0, height);
        let bot = Vec3::new(0.0, 0.0, -height);
        let corners = [
            Vec3::new(radius, 0.0, 0.0),
            Vec3::new(0.0, radius, 0.0),
            Vec3::new(-radius, 0.0, 0.0),
            Vec3::new(0.0, -radius, 0.0),
        ];

        for i in 0..4 {
            let c1 = corners[i];
            let c2 = corners[(i + 1) % 4];
            // Top faces
            self.add_triangle(top, c1, c2);
            // Bottom faces
            self.add_triangle(bot, c2, c1);
        }

        self
    }

    /// Clear all vertices.
    pub fn clear(&mut self) -> &mut Self {
        self.vertices.clear();
        self
    }

    /// Get current vertex count.
    pub fn vertex_count(&self) -> usize {
        self.vertices.len()
    }

    /// Build the final mesh data.
    pub fn build(&self) -> MeshData {
        MeshData {
            vertices: self.vertices.clone(),
        }
    }

    /// Build and consume the builder.
    pub fn finish(self) -> MeshData {
        MeshData {
            vertices: self.vertices,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mesh_builder_triangle() {
        let mut builder = MeshBuilder::new();
        builder.add_triangle(
            Vec3::new(0.0, 0.0, 0.0),
            Vec3::new(1.0, 0.0, 0.0),
            Vec3::new(0.5, 1.0, 0.0),
        );
        let mesh = builder.build();
        assert_eq!(mesh.vertex_count(), 3);
    }

    #[test]
    fn test_mesh_builder_box() {
        let mut builder = MeshBuilder::new();
        builder.add_box(1.0, 1.0, 1.0);
        let mesh = builder.build();
        // 6 faces * 2 triangles * 3 vertices = 36
        assert_eq!(mesh.vertex_count(), 36);
    }

    #[test]
    fn test_mesh_builder_octahedron() {
        let mut builder = MeshBuilder::new();
        builder.add_octahedron(1.0);
        let mesh = builder.build();
        // 8 faces * 3 vertices = 24
        assert_eq!(mesh.vertex_count(), 24);
    }

    #[test]
    fn test_mesh_builder_cylinder() {
        let mut builder = MeshBuilder::new();
        builder.add_cylinder(1.0, 2.0, 8);
        let mesh = builder.build();
        // 8 segments * (2 side triangles + 2 cap triangles) * 3 vertices = 96
        assert_eq!(mesh.vertex_count(), 8 * 4 * 3);
    }
}
