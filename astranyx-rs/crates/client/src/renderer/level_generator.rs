//! Procedural level generator for Astranyx.
//!
//! Generates glTF-compatible level data programmatically.
//! Used for creating test levels and procedural content.

use glam::Vec3;

use astranyx_core::level::{
    CollisionWorld, LevelLight, LevelLightType, LevelMesh, MeshTransform, RenderMesh,
};

/// Builder for creating procedural levels.
pub struct LevelBuilder {
    render_meshes: Vec<RenderMesh>,
    collision_world: CollisionWorld,
    lights: Vec<LevelLight>,
    next_mesh_id: u32,
}

impl Default for LevelBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl LevelBuilder {
    /// Create a new empty level builder.
    pub fn new() -> Self {
        Self {
            render_meshes: Vec::new(),
            collision_world: CollisionWorld::new(),
            lights: Vec::new(),
            next_mesh_id: 0,
        }
    }

    /// Add a box (wall/floor/ceiling) to the level.
    /// Adds both render and collision geometry.
    pub fn add_box(
        &mut self,
        name: &str,
        position: Vec3,
        size: Vec3,
        color: [u8; 3],
    ) -> &mut Self {
        let transform = MeshTransform {
            position,
            rotation: Vec3::ZERO,
            scale: Vec3::ONE,
        };

        // Create box mesh data
        let (positions, normals, indices) = create_box_mesh(size);

        // Add render mesh
        self.render_meshes.push(RenderMesh {
            name: name.to_string(),
            positions: positions.clone(),
            normals,
            indices,
            transform,
            color,
        });

        // Add collision (AABB box is most efficient)
        self.collision_world.add_box(
            &format!("{}_col", name),
            position,
            size * 0.5, // half-extents
        );

        self
    }

    /// Add a wall segment by specifying start and end points.
    pub fn add_wall(
        &mut self,
        start: Vec3,
        end: Vec3,
        height: f32,
        thickness: f32,
        color: [u8; 3],
    ) -> &mut Self {
        let center = (start + end) * 0.5;
        let direction = end - start;
        let length = direction.length();

        // Calculate rotation (around Y axis)
        let angle = direction.z.atan2(direction.x);

        let name = format!("wall_{}", self.next_mesh_id);
        self.next_mesh_id += 1;

        let transform = MeshTransform {
            position: center + Vec3::new(0.0, height * 0.5, 0.0),
            rotation: Vec3::new(0.0, angle, 0.0),
            scale: Vec3::ONE,
        };

        let size = Vec3::new(length, height, thickness);
        let (positions, normals, indices) = create_box_mesh(size);

        self.render_meshes.push(RenderMesh {
            name: name.clone(),
            positions,
            normals,
            indices,
            transform,
            color,
        });

        // Add collision box
        self.collision_world.add_box(
            &format!("{}_col", name),
            transform.position,
            size * 0.5,
        );

        self
    }

    /// Add a floor plane.
    pub fn add_floor(
        &mut self,
        center: Vec3,
        width: f32,
        depth: f32,
        color: [u8; 3],
    ) -> &mut Self {
        let name = format!("floor_{}", self.next_mesh_id);
        self.next_mesh_id += 1;

        self.add_box(&name, center, Vec3::new(width, 0.2, depth), color)
    }

    /// Add a pillar/column.
    pub fn add_pillar(
        &mut self,
        position: Vec3,
        radius: f32,
        height: f32,
        color: [u8; 3],
    ) -> &mut Self {
        let name = format!("pillar_{}", self.next_mesh_id);
        self.next_mesh_id += 1;

        // Use octagonal prism for pillars (cheaper than true cylinder)
        let transform = MeshTransform {
            position: position + Vec3::new(0.0, height * 0.5, 0.0),
            rotation: Vec3::ZERO,
            scale: Vec3::ONE,
        };

        let (positions, normals, indices) = create_octagon_prism(radius, height);

        self.render_meshes.push(RenderMesh {
            name: name.clone(),
            positions: positions.clone(),
            normals,
            indices,
            transform,
            color,
        });

        // Use convex hull for collision
        self.collision_world.add_convex_hull(&format!("{}_col", name), positions, transform);

        self
    }

    /// Add a crate/box obstacle.
    pub fn add_crate(
        &mut self,
        position: Vec3,
        size: f32,
        color: [u8; 3],
    ) -> &mut Self {
        let name = format!("crate_{}", self.next_mesh_id);
        self.next_mesh_id += 1;

        self.add_box(
            &name,
            position + Vec3::new(0.0, size * 0.5, 0.0),
            Vec3::splat(size),
            color,
        )
    }

    /// Add a point light.
    pub fn add_point_light(
        &mut self,
        name: &str,
        position: Vec3,
        color: [u8; 3],
        intensity: f32,
        range: f32,
    ) -> &mut Self {
        self.lights.push(LevelLight {
            name: name.to_string(),
            light_type: LevelLightType::Point,
            position,
            color,
            intensity,
            range,
        });
        self
    }

    /// Add a spot light.
    pub fn add_spot_light(
        &mut self,
        name: &str,
        position: Vec3,
        color: [u8; 3],
        intensity: f32,
        range: f32,
        angle_degrees: u32,
    ) -> &mut Self {
        self.lights.push(LevelLight {
            name: name.to_string(),
            light_type: LevelLightType::Spot { angle: angle_degrees },
            position,
            color,
            intensity,
            range,
        });
        self
    }

    /// Build the final LevelMesh.
    pub fn build(self) -> LevelMesh {
        tracing::info!(
            "Built procedural level: {} render meshes, {} collision shapes, {} lights",
            self.render_meshes.len(),
            self.collision_world.shapes().len(),
            self.lights.len()
        );

        LevelMesh {
            render_meshes: self.render_meshes,
            collision_world: self.collision_world,
            lights: self.lights,
        }
    }
}

/// Create a maze level (like 4_base).
/// The maze is defined by a 2D grid where '#' is wall and '.' is floor.
pub fn create_maze_level(
    maze: &[&str],
    cell_size: f32,
    wall_height: f32,
    floor_color: [u8; 3],
    wall_color: [u8; 3],
) -> LevelMesh {
    let mut builder = LevelBuilder::new();

    let rows = maze.len();
    let cols = maze.first().map(|s| s.len()).unwrap_or(0);

    // Calculate offset to center the maze
    let offset_x = -(cols as f32 * cell_size) / 2.0;
    let offset_z = -(rows as f32 * cell_size) / 2.0;

    // Add floor for entire maze
    builder.add_floor(
        Vec3::new(0.0, -0.1, 0.0),
        cols as f32 * cell_size + cell_size,
        rows as f32 * cell_size + cell_size,
        floor_color,
    );

    // Add walls
    for (row, line) in maze.iter().enumerate() {
        for (col, ch) in line.chars().enumerate() {
            if ch == '#' {
                let x = offset_x + col as f32 * cell_size + cell_size / 2.0;
                let z = offset_z + row as f32 * cell_size + cell_size / 2.0;

                builder.add_box(
                    &format!("wall_{}_{}", row, col),
                    Vec3::new(x, wall_height / 2.0, z),
                    Vec3::new(cell_size, wall_height, cell_size),
                    wall_color,
                );
            }
        }
    }

    // Add ambient lighting
    builder.add_point_light(
        "main_light",
        Vec3::new(0.0, wall_height * 1.5, 0.0),
        [255, 255, 240], // Warm white
        2.0,
        cols as f32 * cell_size,
    );

    // Add corner lights
    let corner_offset = (cols as f32 * cell_size) / 3.0;
    for (i, (dx, dz)) in [(-1.0, -1.0), (1.0, -1.0), (-1.0, 1.0), (1.0, 1.0)].iter().enumerate() {
        builder.add_point_light(
            &format!("corner_light_{}", i),
            Vec3::new(dx * corner_offset, wall_height * 0.8, dz * corner_offset),
            [200, 200, 255], // Cool white
            1.0,
            corner_offset,
        );
    }

    builder.build()
}

/// Create the 4_base test level (MGS-style base infiltration).
pub fn create_4_base_level() -> LevelMesh {
    // Define the maze layout
    // '#' = wall, '.' = floor, 'S' = start, 'E' = end/exit
    let maze = [
        "################",
        "#S.....#.......#",
        "#.####.#.#####.#",
        "#.#....#.#...#.#",
        "#.#.####.#.#.#.#",
        "#.#....#...#.#.#",
        "#.####.#####.#.#",
        "#......#.....#.#",
        "#.######.###.#.#",
        "#........#.#...#",
        "#.########.###.#",
        "#..........#..E#",
        "################",
    ];

    create_maze_level(
        &maze,
        3.0,   // cell_size (3 meters per cell)
        3.0,   // wall_height (3 meters tall)
        [80, 80, 90],    // floor_color (dark gray-blue)
        [60, 65, 70],    // wall_color (darker gray)
    )
}

// Helper functions for mesh generation

/// Create box mesh vertices, normals, and indices.
fn create_box_mesh(size: Vec3) -> (Vec<Vec3>, Vec<Vec3>, Vec<u32>) {
    let hw = size.x / 2.0;
    let hh = size.y / 2.0;
    let hd = size.z / 2.0;

    let mut positions = Vec::new();
    let mut normals = Vec::new();
    let mut indices = Vec::new();

    // Front face (+Z)
    let base = positions.len() as u32;
    positions.extend([
        Vec3::new(-hw, -hh, hd),
        Vec3::new(hw, -hh, hd),
        Vec3::new(hw, hh, hd),
        Vec3::new(-hw, hh, hd),
    ]);
    normals.extend([Vec3::Z; 4]);
    indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

    // Back face (-Z)
    let base = positions.len() as u32;
    positions.extend([
        Vec3::new(hw, -hh, -hd),
        Vec3::new(-hw, -hh, -hd),
        Vec3::new(-hw, hh, -hd),
        Vec3::new(hw, hh, -hd),
    ]);
    normals.extend([Vec3::NEG_Z; 4]);
    indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

    // Top face (+Y)
    let base = positions.len() as u32;
    positions.extend([
        Vec3::new(-hw, hh, hd),
        Vec3::new(hw, hh, hd),
        Vec3::new(hw, hh, -hd),
        Vec3::new(-hw, hh, -hd),
    ]);
    normals.extend([Vec3::Y; 4]);
    indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

    // Bottom face (-Y)
    let base = positions.len() as u32;
    positions.extend([
        Vec3::new(-hw, -hh, -hd),
        Vec3::new(hw, -hh, -hd),
        Vec3::new(hw, -hh, hd),
        Vec3::new(-hw, -hh, hd),
    ]);
    normals.extend([Vec3::NEG_Y; 4]);
    indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

    // Right face (+X)
    let base = positions.len() as u32;
    positions.extend([
        Vec3::new(hw, -hh, hd),
        Vec3::new(hw, -hh, -hd),
        Vec3::new(hw, hh, -hd),
        Vec3::new(hw, hh, hd),
    ]);
    normals.extend([Vec3::X; 4]);
    indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

    // Left face (-X)
    let base = positions.len() as u32;
    positions.extend([
        Vec3::new(-hw, -hh, -hd),
        Vec3::new(-hw, -hh, hd),
        Vec3::new(-hw, hh, hd),
        Vec3::new(-hw, hh, -hd),
    ]);
    normals.extend([Vec3::NEG_X; 4]);
    indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);

    (positions, normals, indices)
}

/// Create an octagonal prism (8-sided cylinder approximation).
fn create_octagon_prism(radius: f32, height: f32) -> (Vec<Vec3>, Vec<Vec3>, Vec<u32>) {
    const SIDES: usize = 8;
    let mut positions = Vec::new();
    let mut normals = Vec::new();
    let mut indices = Vec::new();

    let half_height = height / 2.0;

    // Generate vertices for top and bottom faces
    for i in 0..SIDES {
        let angle = (i as f32 / SIDES as f32) * std::f32::consts::TAU;
        let x = angle.cos() * radius;
        let z = angle.sin() * radius;

        // Bottom vertex
        positions.push(Vec3::new(x, -half_height, z));
        // Top vertex
        positions.push(Vec3::new(x, half_height, z));
    }

    // Side faces
    for i in 0..SIDES {
        let next = (i + 1) % SIDES;
        let base = positions.len() as u32;

        // Get corner positions
        let bl = i * 2;       // bottom-left
        let br = next * 2;    // bottom-right
        let tl = i * 2 + 1;   // top-left
        let tr = next * 2 + 1; // top-right

        // Calculate normal for this face
        let angle = ((i as f32 + 0.5) / SIDES as f32) * std::f32::consts::TAU;
        let normal = Vec3::new(angle.cos(), 0.0, angle.sin());

        // Add face vertices (duplicate for flat shading)
        positions.extend([
            positions[bl],
            positions[br],
            positions[tr],
            positions[tl],
        ]);
        normals.extend([normal; 4]);
        indices.extend([base, base + 1, base + 2, base, base + 2, base + 3]);
    }

    // Top cap
    let top_center_idx = positions.len() as u32;
    positions.push(Vec3::new(0.0, half_height, 0.0));
    normals.push(Vec3::Y);
    for i in 0..SIDES {
        let angle = (i as f32 / SIDES as f32) * std::f32::consts::TAU;
        let x = angle.cos() * radius;
        let z = angle.sin() * radius;
        positions.push(Vec3::new(x, half_height, z));
        normals.push(Vec3::Y);
    }
    for i in 0..SIDES {
        let next = (i + 1) % SIDES;
        indices.extend([
            top_center_idx,
            top_center_idx + 1 + i as u32,
            top_center_idx + 1 + next as u32,
        ]);
    }

    // Bottom cap
    let bot_center_idx = positions.len() as u32;
    positions.push(Vec3::new(0.0, -half_height, 0.0));
    normals.push(Vec3::NEG_Y);
    for i in 0..SIDES {
        let angle = (i as f32 / SIDES as f32) * std::f32::consts::TAU;
        let x = angle.cos() * radius;
        let z = angle.sin() * radius;
        positions.push(Vec3::new(x, -half_height, z));
        normals.push(Vec3::NEG_Y);
    }
    for i in 0..SIDES {
        let next = (i + 1) % SIDES;
        indices.extend([
            bot_center_idx,
            bot_center_idx + 1 + next as u32,
            bot_center_idx + 1 + i as u32,
        ]);
    }

    (positions, normals, indices)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_box_mesh() {
        let (positions, normals, indices) = create_box_mesh(Vec3::new(2.0, 2.0, 2.0));

        // 6 faces * 4 vertices = 24 vertices
        assert_eq!(positions.len(), 24);
        assert_eq!(normals.len(), 24);
        // 6 faces * 2 triangles * 3 indices = 36 indices
        assert_eq!(indices.len(), 36);
    }

    #[test]
    fn test_level_builder() {
        let mut builder = LevelBuilder::new();
        builder
            .add_box("test_wall", Vec3::ZERO, Vec3::ONE, [128, 128, 128])
            .add_point_light("test_light", Vec3::new(0.0, 2.0, 0.0), [255, 255, 255], 1.0, 10.0);

        let level = builder.build();
        assert_eq!(level.render_meshes.len(), 1);
        assert_eq!(level.collision_world.shapes().len(), 1);
        assert_eq!(level.lights.len(), 1);
    }

    #[test]
    fn test_create_maze_level() {
        let maze = [
            "###",
            "#.#",
            "###",
        ];

        let level = create_maze_level(&maze, 1.0, 2.0, [100, 100, 100], [50, 50, 50]);

        // Should have floor + 8 wall blocks
        assert!(level.render_meshes.len() >= 9);
        // Should have lights
        assert!(!level.lights.is_empty());
    }
}
