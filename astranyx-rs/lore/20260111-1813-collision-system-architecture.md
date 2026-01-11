# Collision System Architecture: Boxes + Convex Hulls

## Summary

The Astranyx collision system uses a **hybrid approach** combining **AABB boxes** for simple geometry and **convex hulls** for irregular shapes. This follows the proven design patterns from classic stealth/FPS games like Quake, Metal Gear Solid, and modern engines, while maintaining **determinism** for P2P lockstep netcode.

## Design Principles

### 1. Separate Visual and Collision Geometry

```
┌─────────────────────────────────────────────────────────────┐
│  VISUAL MESH (High Detail)      COLLISION MESH (Simplified) │
│                                                             │
│       ╔══════╗                        ┌────────┐            │
│      ╔╝      ╚╗                       │        │            │
│     ╔╝ pillar ╚╗  ────────►           │  box   │            │
│    ╔╝          ╚╗                     │        │            │
│    ╚════════════╝                     └────────┘            │
│                                                             │
│   Rendered by three-d            Used by parry3d           │
└─────────────────────────────────────────────────────────────┘
```

### 2. Collision Shape Hierarchy

| Shape Type | Use Case | Performance | Determinism |
|------------|----------|-------------|-------------|
| **Box (AABB)** | Walls, floors, crates | Fastest | Fully deterministic |
| **Convex Hull** | Pillars, irregular objects | Fast | Deterministic |
| **Trimesh** | Complex terrain (last resort) | Slowest | Deterministic |

**Recommendation**: 90% boxes, 10% convex hulls, avoid trimesh.

## Implementation

### Core Types (`crates/core/src/level/mesh.rs`)

```rust
/// Individual collision shape types.
pub enum CollisionShape {
    /// Axis-aligned bounding box - fastest collision detection.
    Box {
        name: String,
        center: Vec3,
        half_extents: Vec3,
    },
    /// Convex hull from vertices - for irregular shapes.
    ConvexHull {
        name: String,
        vertices: Vec<Vec3>,
        transform: MeshTransform,
    },
    /// Triangle mesh - slowest, use sparingly.
    Trimesh {
        name: String,
        vertices: Vec<Vec3>,
        indices: Vec<[u32; 3]>,
        transform: MeshTransform,
    },
}
```

### CollisionWorld Container

```rust
pub struct CollisionWorld {
    shapes: Vec<CollisionShape>,
    // Future: BVH tree for spatial queries
}

impl CollisionWorld {
    pub fn add_box(&mut self, name: &str, center: Vec3, half_extents: Vec3);
    pub fn add_convex_hull(&mut self, name: &str, vertices: Vec<Vec3>, transform: MeshTransform);
    pub fn raycast(&self, origin: Vec3, direction: Vec3, max_dist: f32) -> Option<f32>;
    pub fn resolve_capsule_collision(&self, position: Vec3, radius: f32, height: f32) -> Vec3;
}
```

### Player Collision (Capsule)

The player is represented as a **vertical capsule** (cylinder with hemisphere caps):

```
       ___
      /   \     ← height/2 sphere
     |     |
     |  ●  |    ← center at position.y + height/2
     |     |
      \___/     ← height/2 sphere

     ←───→ radius (0.5m default)
```

Parameters:
- `PLAYER_RADIUS = 0.5` (50cm)
- `PLAYER_HEIGHT = 1.8` (1.8m standing)
- Crouching reduces height to 1.08m (60%)

## File Format Strategy

### Option A: glTF with Naming Convention (Current)

```
assets/levels/4_base.glb
├── Wall_001        → visual mesh
├── Wall_001_col    → collision mesh (suffix indicates collision)
├── Pillar_002      → visual mesh
└── Pillar_002_col  → collision convex hull
```

### Option B: Rhai Geometry (Legacy/Development)

```rhai
geometry: [
    #{ type: "box", pos: #{ x: 0.0, y: 22.5, z: 0.0 },
       size: #{ x: 400.0, y: 45.0, z: 5.0 },
       color: #{ r: 60, g: 55, b: 65 }, solid: true },
]
```

### Option C: Procedural Generation

```rust
let mut builder = LevelBuilder::new();
builder
    .add_floor(Vec3::ZERO, 50.0, 50.0, [80, 80, 90])
    .add_box("wall", Vec3::new(10.0, 1.5, 0.0), Vec3::new(2.0, 3.0, 20.0), [60, 65, 70])
    .add_pillar(Vec3::new(5.0, 0.0, 5.0), 0.5, 3.0, [100, 100, 100]);
```

## Collision Resolution Algorithm

### Box-Capsule Collision

```rust
fn capsule_penetration(&self, capsule_pos: Vec3, radius: f32, height: f32) -> Option<Vec3> {
    // 1. Expand box by capsule radius in XZ plane
    let expanded_half = Vec3::new(
        half_extents.x + radius,
        half_extents.y,
        half_extents.z + radius,
    );

    // 2. Check Y overlap (capsule bottom to top)
    if capsule_top < box_bottom || capsule_bottom > box_top {
        return None;  // No vertical overlap
    }

    // 3. Check XZ containment
    if point_in_expanded_box_xz(capsule_pos) {
        // 4. Find shortest push-out direction
        let to_left = capsule_pos.x - (center.x - expanded_half.x);
        let to_right = (center.x + expanded_half.x) - capsule_pos.x;
        let to_back = capsule_pos.z - (center.z - expanded_half.z);
        let to_front = (center.z + expanded_half.z) - capsule_pos.z;

        // Push out in minimum direction
        return Some(min_direction_push(to_left, to_right, to_back, to_front));
    }
    None
}
```

### Convex Hull Collision (via parry3d)

```rust
fn capsule_penetration(&self, capsule_pos: Vec3, radius: f32, height: f32) -> Option<Vec3> {
    let capsule = parry3d::shape::Capsule::new_y(height / 2.0, radius);
    let hull = SharedShape::convex_hull(&vertices)?;

    if let Ok(Some(contact)) = query::contact(&capsule_iso, &capsule, &hull_iso, &hull, 0.0) {
        let penetration = contact.dist.abs();
        let normal = contact.normal1.into_inner();
        return Some(Vec3::new(normal.x, normal.y, normal.z) * penetration);
    }
    None
}
```

## Dual Backend Support

The FPS collision system supports both legacy Rhai geometry and modern CollisionWorld:

```rust
pub enum CollisionBackend<'a> {
    Legacy(&'a [GeometryDef]),     // Rhai scripts (current)
    Modern(&'a CollisionWorld),    // glTF/procedural (future)
}

impl CollisionBackend<'_> {
    pub fn resolve_collision(&self, position: Vec3, radius: f32, height: f32) -> Vec3;
    pub fn raycast(&self, origin: Vec3, direction: Vec3, max_dist: f32) -> Option<f32>;
}
```

## Historical Context

| Game | Year | Collision Approach |
|------|------|-------------------|
| Quake | 1996 | BSP with convex brushes |
| Metal Gear Solid | 1998 | Simplified collision meshes |
| Half-Life 2 | 2004 | BSP + convex decomposition |
| Modern engines | 2020s | Visual + collision + convex hulls |

## Dependencies

```toml
# crates/core/Cargo.toml (deterministic simulation)
parry3d = "0.17"  # Collision queries only, no physics solver

# crates/client/Cargo.toml (visual effects only)
rapier3d = "0.22"  # Full physics for debris/particles
gltf = { version = "1.4", features = ["KHR_lights_punctual"] }
```

## Determinism Guarantee

**CRITICAL**: Rapier's `PhysicsPipeline::step()` is NOT deterministic due to floating-point accumulation.

Solution:
1. Use `parry3d` (Rapier's collision library) directly for queries
2. Manual collision resolution with deterministic math
3. Only use `QueryPipeline` for read-only shape queries
4. Rapier physics ONLY for client-side visual effects (debris, particles)

## Future Improvements

1. **BVH Tree**: Add spatial acceleration structure for many shapes
2. **Rotation Support**: Handle rotated collision boxes
3. **Stairs/Ramps**: Automatic step-up for small obstacles
4. **Crouch Detection**: Prevent standing in low spaces
5. **Trigger Volumes**: Non-solid shapes for events

## References

- [parry3d docs](https://docs.rs/parry3d)
- [Quake BSP Format](https://www.gamers.org/dEngine/quake/spec/quake-spec34/qkspec_4.htm)
- [GJK Algorithm](https://en.wikipedia.org/wiki/Gilbert-Johnson-Keerthi_distance_algorithm)
