# glTF Level Mesh System Implementation

## Summary

Implemented a modern level mesh system using **glTF** format for 3D asset interchange and **parry3d** for deterministic collision detection. This replaces inline Rhai geometry definitions with external mesh files.

## Architecture

```
Blender/Procedural → .glb file → Client loads → Core collision
                         ↓
                   Render meshes → three-d GPU
                         ↓
                   Collision meshes → parry3d BVH
```

### Separation of Concerns

| Crate | Purpose | Library |
|-------|---------|---------|
| `astranyx-core` | Deterministic collision queries | parry3d |
| `astranyx-client` | Visual rendering | three-d + gltf |

## New Files

### Core Crate (`crates/core/src/`)

- **`level/mesh.rs`** - Level mesh and collision types
  - `LevelMesh` - Complete level (render meshes + collision world + lights)
  - `RenderMesh` - Visual mesh with positions, normals, indices, transform
  - `CollisionWorld` - parry3d-backed collision container
  - `CollisionShape` - Box, ConvexHull, or Trimesh collision primitives
  - `LevelLight` - Point, Spot, or Directional light definitions

### Client Crate (`crates/client/src/renderer/`)

- **`gltf_loader.rs`** - glTF/GLB file parser
  - `load_gltf_level(path)` - Load from file
  - `load_gltf_from_bytes(data)` - Load from embedded bytes
  - `render_mesh_to_cpu_mesh()` - Convert to three-d format
  - Supports KHR_lights_punctual extension

- **`level_generator.rs`** - Procedural level builder
  - `LevelBuilder` - Fluent API for creating levels
  - `create_maze_level()` - Generate maze from ASCII art
  - `create_4_base_level()` - MGS-style base infiltration level

## Collision System

### Dual Backend Support

The FPS collision system now supports both backends:

```rust
pub enum CollisionBackend<'a> {
    Legacy(&'a [GeometryDef]),     // Rhai scripts
    Modern(&'a CollisionWorld),    // glTF/procedural
}

impl CollisionBackend<'_> {
    pub fn resolve_collision(&self, position: Vec3, radius: f32, height: f32) -> Vec3;
    pub fn raycast(&self, origin: Vec3, direction: Vec3, max_dist: f32) -> Option<f32>;
}
```

### Collision Shape Types

| Type | Use Case | Performance |
|------|----------|-------------|
| Box (AABB) | Walls, floors | Fastest |
| ConvexHull | Pillars, irregular objects | Fast |
| Trimesh | Complex terrain | Slowest |

## Usage

### Procedural Level Generation

```rust
use crate::renderer::level_generator::{LevelBuilder, create_4_base_level};

// Fluent API
let mut builder = LevelBuilder::new();
builder
    .add_floor(Vec3::ZERO, 50.0, 50.0, [80, 80, 90])
    .add_box("wall1", Vec3::new(10.0, 1.5, 0.0), Vec3::new(2.0, 3.0, 20.0), [60, 65, 70])
    .add_pillar(Vec3::new(5.0, 0.0, 5.0), 0.5, 3.0, [100, 100, 100])
    .add_point_light("light1", Vec3::new(0.0, 4.0, 0.0), [255, 255, 240], 2.0, 30.0);
let level = builder.build();

// Or use preset maze
let base_level = create_4_base_level();
```

### Loading glTF Files

```rust
use crate::renderer::gltf_loader::load_gltf_level;

let level = load_gltf_level("assets/levels/4_base.glb")?;
```

### Rendering

```rust
render_level_mesh(context, &level, camera, lights, frame_input);
```

## Blender Workflow (Future)

### Naming Convention

```
Wall_001        → render mesh (high detail)
Wall_001_col    → collision mesh (simplified)
```

### Export Settings

1. Format: GLB (Binary glTF)
2. Include: Normals, Materials
3. Lights: Enable KHR_lights_punctual

## Dependencies Added

```toml
# crates/core/Cargo.toml
parry3d = "0.17"

# crates/client/Cargo.toml
gltf = { version = "1.4", features = ["KHR_lights_punctual"] }
thiserror = "2.0"
```

## Testing

All tests pass:

```bash
cargo test --package astranyx-core   # Collision tests
cargo test --package astranyx-client # glTF loader tests
```

## Future Work

1. Rotation support in mesh transforms (quaternion → matrix)
2. Texture support from glTF materials
3. Integration with game loop (replace inline geometry)
4. Spot/Directional light rendering
5. Blender workflow documentation
