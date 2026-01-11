//! glTF level loader for Astranyx.
//!
//! Loads .glb/.gltf files and extracts:
//! - Render meshes for three-d visualization
//! - Collision meshes (identified by `_col` suffix) for physics
//! - Lights from KHR_lights_punctual extension

use std::path::Path;

use glam::Vec3;

use astranyx_core::level::{
    CollisionWorld, LevelLight, LevelLightType, LevelMesh, MeshTransform, RenderMesh,
};

/// Error type for glTF loading.
#[derive(Debug, thiserror::Error)]
pub enum GltfError {
    #[error("Failed to load glTF file: {0}")]
    LoadError(#[from] gltf::Error),

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    #[error("Missing position data for mesh: {0}")]
    MissingPositions(String),

    #[error("Missing buffer data")]
    MissingBufferData,
}

/// Load a glTF/GLB file and extract level data.
///
/// Naming conventions:
/// - `Mesh_name` → render mesh only
/// - `Mesh_name_col` → collision mesh (simplified)
///
/// If both exist, the visual mesh is rendered and collision mesh is used for physics.
/// If only a non-`_col` mesh exists, it's used for both render and collision.
pub fn load_gltf_level(path: impl AsRef<Path>) -> Result<LevelMesh, GltfError> {
    let path = path.as_ref();
    let (document, buffers, _images) = gltf::import(path)?;

    let mut render_meshes = Vec::new();
    let mut collision_world = CollisionWorld::new();
    let mut lights = Vec::new();

    // Process all nodes in the scene
    for scene in document.scenes() {
        for node in scene.nodes() {
            process_node(&node, &buffers, &mut render_meshes, &mut collision_world)?;
        }
    }

    // Extract lights from KHR_lights_punctual extension
    if let Some(lights_ext) = document.lights() {
        for (idx, light) in lights_ext.enumerate() {
            // Find the node that references this light
            let light_node = document.nodes().find(|n| {
                n.light().map(|l| l.index() == idx).unwrap_or(false)
            });

            let position = light_node
                .map(|n| {
                    let t = n.transform().decomposed().0;
                    Vec3::new(t[0], t[1], t[2])
                })
                .unwrap_or(Vec3::ZERO);

            let color = light.color();
            let intensity = light.intensity();
            let range = light.range().unwrap_or(100.0);

            let light_type = match light.kind() {
                gltf::khr_lights_punctual::Kind::Point => LevelLightType::Point,
                gltf::khr_lights_punctual::Kind::Spot { inner_cone_angle: _, outer_cone_angle } => {
                    LevelLightType::Spot {
                        angle: (outer_cone_angle.to_degrees() as u32).max(1),
                    }
                }
                gltf::khr_lights_punctual::Kind::Directional => LevelLightType::Directional,
            };

            lights.push(LevelLight {
                name: light.name().unwrap_or("light").to_string(),
                light_type,
                position,
                color: [
                    (color[0] * 255.0) as u8,
                    (color[1] * 255.0) as u8,
                    (color[2] * 255.0) as u8,
                ],
                intensity,
                range,
            });
        }
    }

    tracing::info!(
        "Loaded glTF level: {} render meshes, {} collision shapes, {} lights",
        render_meshes.len(),
        collision_world.shapes().len(),
        lights.len()
    );

    Ok(LevelMesh {
        render_meshes,
        collision_world,
        lights,
    })
}

/// Process a glTF node and its children recursively.
fn process_node(
    node: &gltf::Node,
    buffers: &[gltf::buffer::Data],
    render_meshes: &mut Vec<RenderMesh>,
    collision_world: &mut CollisionWorld,
) -> Result<(), GltfError> {
    // Get node transform
    let (translation, rotation, scale) = node.transform().decomposed();
    let transform = MeshTransform {
        position: Vec3::new(translation[0], translation[1], translation[2]),
        rotation: quat_to_euler(rotation),
        scale: Vec3::new(scale[0], scale[1], scale[2]),
    };

    // Process mesh if present
    if let Some(mesh) = node.mesh() {
        let name = mesh.name().unwrap_or("unnamed").to_string();
        let is_collision = name.ends_with("_col");

        for primitive in mesh.primitives() {
            let (positions, normals, indices) = extract_primitive_data(&primitive, buffers)?;

            // Get material color (default to gray)
            let color = primitive
                .material()
                .pbr_metallic_roughness()
                .base_color_factor();
            let color_rgb = [
                (color[0] * 255.0) as u8,
                (color[1] * 255.0) as u8,
                (color[2] * 255.0) as u8,
            ];

            if is_collision {
                // Add as collision shape
                // Convert indices from flat to triangles
                let triangle_indices: Vec<[u32; 3]> = indices
                    .chunks(3)
                    .filter_map(|chunk| {
                        if chunk.len() == 3 {
                            Some([chunk[0], chunk[1], chunk[2]])
                        } else {
                            None
                        }
                    })
                    .collect();

                // Try to create convex hull first, fall back to trimesh
                if positions.len() <= 256 {
                    // Small enough for convex hull
                    collision_world.add_convex_hull(&name, positions.clone(), transform);
                } else {
                    // Large mesh - use trimesh
                    collision_world.add_trimesh(&name, positions.clone(), triangle_indices, transform);
                }
            } else {
                // Add as render mesh
                render_meshes.push(RenderMesh {
                    name: name.clone(),
                    positions,
                    normals,
                    indices,
                    transform,
                    color: color_rgb,
                });
            }
        }
    }

    // Process children
    for child in node.children() {
        process_node(&child, buffers, render_meshes, collision_world)?;
    }

    Ok(())
}

/// Extract vertex positions, normals, and indices from a glTF primitive.
fn extract_primitive_data(
    primitive: &gltf::Primitive,
    buffers: &[gltf::buffer::Data],
) -> Result<(Vec<Vec3>, Vec<Vec3>, Vec<u32>), GltfError> {
    let reader = primitive.reader(|buffer| Some(&buffers[buffer.index()]));

    // Extract positions (required)
    let positions: Vec<Vec3> = reader
        .read_positions()
        .ok_or_else(|| GltfError::MissingPositions("primitive".to_string()))?
        .map(|p| Vec3::new(p[0], p[1], p[2]))
        .collect();

    // Extract normals (generate if missing)
    let normals: Vec<Vec3> = reader
        .read_normals()
        .map(|iter| iter.map(|n| Vec3::new(n[0], n[1], n[2])).collect())
        .unwrap_or_else(|| {
            // Generate flat normals if not present
            vec![Vec3::Y; positions.len()]
        });

    // Extract indices (generate if missing)
    let indices: Vec<u32> = reader
        .read_indices()
        .map(|iter| iter.into_u32().collect())
        .unwrap_or_else(|| {
            // Generate sequential indices if not indexed
            (0..positions.len() as u32).collect()
        });

    Ok((positions, normals, indices))
}

/// Convert quaternion [x, y, z, w] to Euler angles [x, y, z] in radians.
fn quat_to_euler(q: [f32; 4]) -> Vec3 {
    let quat = glam::Quat::from_xyzw(q[0], q[1], q[2], q[3]);
    let (x, y, z) = quat.to_euler(glam::EulerRot::XYZ);
    Vec3::new(x, y, z)
}

/// Load embedded glTF data (for procedural levels).
pub fn load_gltf_from_bytes(data: &[u8]) -> Result<LevelMesh, GltfError> {
    let (document, buffers, _images) = gltf::import_slice(data)?;

    let mut render_meshes = Vec::new();
    let mut collision_world = CollisionWorld::new();
    let mut lights = Vec::new();

    // Process all nodes in the scene
    for scene in document.scenes() {
        for node in scene.nodes() {
            process_node(&node, &buffers, &mut render_meshes, &mut collision_world)?;
        }
    }

    // Extract lights (same as load_gltf_level)
    if let Some(lights_ext) = document.lights() {
        for (idx, light) in lights_ext.enumerate() {
            let light_node = document.nodes().find(|n| {
                n.light().map(|l| l.index() == idx).unwrap_or(false)
            });

            let position = light_node
                .map(|n| {
                    let t = n.transform().decomposed().0;
                    Vec3::new(t[0], t[1], t[2])
                })
                .unwrap_or(Vec3::ZERO);

            let color = light.color();
            let intensity = light.intensity();
            let range = light.range().unwrap_or(100.0);

            let light_type = match light.kind() {
                gltf::khr_lights_punctual::Kind::Point => LevelLightType::Point,
                gltf::khr_lights_punctual::Kind::Spot { inner_cone_angle: _, outer_cone_angle } => {
                    LevelLightType::Spot {
                        angle: (outer_cone_angle.to_degrees() as u32).max(1),
                    }
                }
                gltf::khr_lights_punctual::Kind::Directional => LevelLightType::Directional,
            };

            lights.push(LevelLight {
                name: light.name().unwrap_or("light").to_string(),
                light_type,
                position,
                color: [
                    (color[0] * 255.0) as u8,
                    (color[1] * 255.0) as u8,
                    (color[2] * 255.0) as u8,
                ],
                intensity,
                range,
            });
        }
    }

    Ok(LevelMesh {
        render_meshes,
        collision_world,
        lights,
    })
}

/// Convert a RenderMesh to three-d CpuMesh format.
pub fn render_mesh_to_cpu_mesh(mesh: &RenderMesh) -> three_d::CpuMesh {
    let positions: Vec<three_d::Vec3> = mesh
        .positions
        .iter()
        .map(|p| three_d::Vec3::new(p.x, p.y, p.z))
        .collect();

    let normals: Vec<three_d::Vec3> = mesh
        .normals
        .iter()
        .map(|n| three_d::Vec3::new(n.x, n.y, n.z))
        .collect();

    three_d::CpuMesh {
        positions: three_d::Positions::F32(positions),
        normals: Some(normals),
        indices: three_d::Indices::U32(mesh.indices.clone()),
        ..Default::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quat_to_euler() {
        // Identity quaternion should give zero rotation
        let euler = quat_to_euler([0.0, 0.0, 0.0, 1.0]);
        assert!((euler.x.abs() + euler.y.abs() + euler.z.abs()) < 0.001);
    }
}
