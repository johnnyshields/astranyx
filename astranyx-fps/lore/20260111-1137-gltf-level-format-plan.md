# glTF Level Format & Advanced Collision System

## Summary

Moving from inline Rhai geometry definitions to **glTF/GLB** files for level meshes, with **parry3d** for advanced collision detection. This follows modern standards while maintaining P2P lockstep determinism.

## Why glTF?

- **Industry standard**: Used by Bevy, Godot, Unity, Unreal, three.js
- **Rust support**: Mature `gltf` crate (1.4+)
- **Tooling**: Blender exports natively, three-d has import support
- **Open format**: No licensing issues (unlike FBX)

Alternatives considered:
- **BSP (Quake)**: Great for indoor levels but 30 years old, limited tooling
- **USD (Pixar)**: Powerful but complex, poor Rust ecosystem
- **FBX**: Autodesk proprietary, licensing concerns

## Historical Context

| Game | Year | Collision Approach |
|------|------|-------------------|
| Quake | 1996 | BSP with convex brushes |
| Metal Gear Solid | 1998 | Simplified collision meshes separate from visual |
| Modern engines | 2020s | Visual mesh + collision mesh + convex decomposition |

## Architecture

```
Blender → .glb file → Client loads → Core gets collision shapes
                          ↓
                    Render meshes → three-d GPU
                          ↓
                    Collision meshes → parry3d BVH
```

### Key Separation
- **astranyx-core**: Deterministic. Uses parry3d for collision queries only (no physics solver)
- **astranyx-client**: Non-deterministic visual effects stay with Rapier

### Determinism Constraint

Rapier's `PhysicsPipeline::step()` is non-deterministic due to floating-point accumulation. Solution:
- Use `parry3d` (Rapier's collision library) directly
- Only use `QueryPipeline` for read-only shape queries
- Manual collision resolution with deterministic math

## File Format Convention

```
assets/levels/
├── 4_base.glb           # Visual + collision meshes
└── 4_base.level.rhai    # Scripting, spawns, routes
```

### Mesh Naming Convention (in Blender)
```
Wall_001        → render only (detailed)
Wall_001_col    → collision (simplified box/convex)
Pillar_002      → render only
Pillar_002_col  → collision (convex hull)
```

## Collision Types

| Type | Use Case | Performance |
|------|----------|-------------|
| AABB Box | Walls, floors | Fastest |
| Convex Hull | Irregular objects (crates, pillars) | Fast |
| Trimesh | Terrain, stairs (if needed) | Slowest |

Recommended: **Boxes + Convex Hulls** (MGS/Quake style)

## Implementation Phases

### Phase 1: glTF Loading
- Add `gltf = "1.4"` to client
- Create `gltf_loader.rs` for mesh extraction
- Render glTF meshes via three-d

### Phase 2: Collision Extraction
- Parse `_col` suffix meshes as collision
- Convert to `CollisionShape` enum

### Phase 3: Advanced Collision
- Add `parry3d = "0.17"` to core
- Create `CollisionWorld` with BVH
- Player-to-mesh collision with slide response

### Phase 4: Test Level
- Procedurally generate `4_base.glb`
- Replace inline Rhai geometry
- User can later create levels in Blender

## New Dependencies

```toml
# crates/client/Cargo.toml
gltf = "1.4"

# crates/core/Cargo.toml
parry3d = "0.17"
```

## New Files

| File | Purpose |
|------|---------|
| `client/src/renderer/gltf_loader.rs` | glTF parsing, mesh extraction |
| `client/src/renderer/level_generator.rs` | Procedural glTF generation |
| `core/src/level/mesh.rs` | LevelMesh, CollisionShape types |
| `assets/levels/4_base.glb` | Test level mesh |

## Blender Workflow (Future)

1. Create visual mesh (detailed geometry)
2. Duplicate, simplify for collision
3. Name collision objects with `_col` suffix
4. Set collision objects to non-renderable
5. Export as `.glb` (binary glTF, embedded textures)

## References

- [glTF Specification](https://www.khronos.org/gltf/)
- [parry3d docs](https://docs.rs/parry3d)
- [gltf crate](https://docs.rs/gltf)
- [Bevy glTF loading](https://bevy-cheatbook.github.io/3d/gltf.html)
