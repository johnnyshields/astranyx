# Rust Rendering System Port

**Date**: 2026-01-09
**Status**: Complete

## Summary

Ported the TypeScript rendering system to Rust/wgpu with full camera, mesh, shader, and HUD support.

## Files Created

### Camera System (`crates/client/src/renderer/camera.rs`)
- 2.5D Einhänder-style camera with configurable tilt angle
- Perspective projection with play bounds calculation
- NDC to world coordinate conversion for entity bounds
- Uses glam::Mat4 for all matrix operations

### Mesh System (`crates/client/src/renderer/mesh.rs`)
- `MeshVertex` struct with position + normal (bytemuck-compatible)
- `MeshBuilder` fluent API for procedural geometry:
  - `add_triangle()` - automatic normal calculation
  - `add_quad()` - two triangles
  - `add_box()` - 6-face cube
  - `add_cylinder()` - configurable segments
  - `add_cone()` - configurable segments
  - `add_octahedron()` - diamond shape
  - `add_pyramid()` - double pyramid

### Mesh Generators (`crates/client/src/renderer/meshes.rs`)
- `create_player_ship_mesh()` - fighter jet with canopy, wings, tail fin
- `create_enemy_ship_mesh()` - angular X-wing style
- `create_tank_mesh()` - boxy with turret
- `create_boss_core_mesh()` - octahedron
- `create_drone_mesh()` - small octahedron
- `create_powerup_mesh()` - diamond
- `create_mine_mesh()` - spiky sphere
- `create_bullet_mesh()` - elongated octahedron
- `create_laser_mesh()` - thin cylinder
- `create_orb_mesh()` - icosahedron

### Phong Shader (`crates/client/src/renderer/shaders/phong.wgsl`)
- WGSL shader matching original WebGL shader
- Blinn-Phong specular lighting
- Rim lighting for sci-fi edge glow
- Energy pulse effect (sin-based time animation)
- Global uniforms: projection, view, camera_pos, time
- Instance uniforms: model matrix, normal matrix, color

### Phong Pipeline (`crates/client/src/renderer/phong_pipeline.rs`)
- `GlobalUniforms` and `InstanceUniforms` structs (bytemuck-compatible)
- Bind group layouts for global (group 0) and per-instance (group 1)
- Depth testing with Depth32Float format
- Alpha blending enabled

### HUD System (`crates/client/src/hud/`)
- **mod.rs**: Platform-agnostic trait and types
  - `HudPlayerState` - shields, lives, level, score
  - `HudGameState` - boss health, enemy count
  - `WeaponSlot` - name, ammo, color
  - `Hud` trait for platform-specific implementations

- **web.rs**: WASM implementation using web-sys Canvas 2D API
  - Creates overlay `<canvas id="hud-canvas">` on init
  - 5:3 letterbox/pillarbox viewport matching
  - Device pixel ratio handling for high-DPI
  - Player HUD: shield bar, lives, level indicators
  - Game HUD: boss health bar with warning
  - Weapon slots with ammo bars
  - Health bars and weapon labels at screen positions

- **native.rs**: Placeholder for native text rendering
  - Could use wgpu_glyph or egui in future

### Renderer Updates (`crates/client/src/renderer/mod.rs`)
- Integrated PhongPipeline with depth buffer
- `GpuMesh` struct for cached GPU meshes
- `register_mesh()` - upload MeshData to GPU
- `begin_frame()` - update global uniforms
- `draw_mesh()` - draw with position, scale, rotation, color
- Proper depth texture recreation on resize

## Coordinate System

Adopted consistent coordinate system (future-proofed for Starfox-style 3D):
- **X** = forward/backward (scrolling direction)
- **Y** = up/down (screen vertical)
- **Z** = depth (into/out of screen in 2.5D, left/right in 3D)

All mesh generators orient ships with nose pointing +X.

## Dependencies Added

```toml
[dependencies.web-sys]
features = [
    "CanvasRenderingContext2d",  # NEW for HUD
]
```

## Build Targets

All verified working:
- Native Linux: `cargo check --target x86_64-unknown-linux-gnu`
- Native Windows: `cargo build --release --target x86_64-pc-windows-gnu`
- WASM: `wasm-pack build crates/client --target web --features wasm --no-default-features`

## Tests

16 tests passing across all crates:
- `astranyx-core`: 13 tests (random, physics, simulation, input)
- `astranyx-protocol`: 3 tests (codec roundtrips)

## Next Steps

1. Connect simulation to renderer (entity -> mesh mapping)
2. Implement native HUD (wgpu_glyph or egui)
3. Add GLB mesh loading
4. Implement game state rendering loop
