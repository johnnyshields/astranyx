# Three-d Renderer Migration

## Summary

Migrated the Rust client from custom wgpu renderer to **three-d** library. This resolves GPU buffer race conditions that caused entities to render one at a time.

## Decision

Evaluated several options:
- **Bevy** - Full game engine, but ECS lock-in conflicts with deterministic lockstep simulation
- **three-d** - Three.js-like API, simple, smaller binary, no architectural constraints
- **macroquad** - Too simple for 2.5D
- **rend3/luminance** - Mid-level, more complexity than needed

Chose **three-d** because:
1. Deterministic `astranyx-core` simulation stays independent
2. Simple rendering API (meshes, materials, lights, camera)
3. Handles windowing via winit internally
4. Smaller binary than Bevy
5. No ECS lock-in

## Architecture

```
┌─────────────────────────────────────────┐
│           astranyx-client               │
│  - three-d Window + render loop         │
│  - InputState (three-d Key enum)        │
│  - GameRenderer (mesh registry)         │
│  - Renders GameState each frame         │
└─────────────────┬───────────────────────┘
                  │ uses
┌─────────────────▼───────────────────────┐
│           astranyx-core                 │
│  - Simulation (30Hz fixed timestep)     │
│  - GameState (players, enemies, etc.)   │
│  - ScriptEngine (rhai)                  │
│  - Deterministic for lockstep           │
└─────────────────────────────────────────┘
```

## Files Changed

### Created
- `crates/core/src/scripting/mod.rs` - Rhai script engine wrapper
- `crates/client/src/renderer/mod.rs` - three-d mesh management

### Modified
- `Cargo.toml` - Edition 2021, three-d dependency
- `.cargo/config.toml` - Removed `+crt-static` for Linux (caused proc-macro issues)
- `crates/client/Cargo.toml` - three-d, removed winit/wgpu direct deps
- `crates/client/src/lib.rs` - three-d window/rendering loop
- `crates/client/src/game.rs` - Simplified to render info helpers

### Removed
- `crates/client/src/app.rs` - Replaced by lib.rs render loop
- `crates/client/src/wasm.rs` - Placeholder, will reimplement
- `crates/client/src/input/` - Using three-d's Key enum directly

## Key Implementation Details

### Rendering Loop
```rust
window.render_loop(move |mut frame_input| {
    // Handle three-d events
    for event in frame_input.events.iter() {
        match event {
            Event::KeyPress { kind, .. } => input_state.handle_key(*kind, true),
            Event::KeyRelease { kind, .. } => input_state.handle_key(*kind, false),
            _ => {}
        }
    }

    // Fixed timestep simulation
    while accumulated_time >= TICK_DURATION {
        simulation.tick(&inputs);
        accumulated_time -= TICK_DURATION;
    }

    // Render
    frame_input.screen().clear(...);
    render_game_state(...);

    FrameOutput::default()
});
```

### Mesh Registration
Meshes are pre-registered with CPU data, then instantiated per-frame:
```rust
// Registration (once at startup)
renderer.register_mesh("player_ship", &meshes::create_player_ship_mesh());

// Rendering (each frame)
let cpu_mesh = game_renderer.get_mesh(mesh_name);
let gm = Gm::new(Mesh::new(context, cpu_mesh), material);
gm.set_transformation(Mat4::from_translation(position) * Mat4::from_scale(scale));
frame_input.screen().render(camera, &gm, lights);
```

### Input Handling
Using three-d's Key enum directly (wraps winit internally):
```rust
fn handle_key(&mut self, key: Key, pressed: bool) {
    match key {
        Key::W | Key::ArrowUp => self.up = pressed,
        Key::Space | Key::Z => self.fire = pressed,
        // ...
    }
}
```

### Scripting Integration
Fixed Rhai script loading - must run script first to initialize constants before calling functions:
```rust
fn extract_enemy_stats(&self, ast: &AST) -> Option<EnemyStats> {
    let mut scope = Scope::new();
    let _ = self.engine.run_ast_with_scope(&mut scope, ast); // Initialize constants
    let result: Result<Map, _> = self.engine.call_fn(&mut scope, ast, "get_stats", ());
    // ...
}
```

## Build Targets

- Linux: `cargo build --package astranyx-client`
- Windows: `cargo build --package astranyx-client --target x86_64-pc-windows-gnu --release`

## Dependencies

```toml
three-d = "0.18"      # Rendering + windowing
glam = "0.29"         # Math (shared with core)
rhai = "1.21"         # Scripting
tracing = "0.1"       # Logging
anyhow = "1"          # Error handling
```

## Future Work

- WASM support (three-d supports WebGL)
- HUD rendering with three-d's 2D primitives or egui overlay
- Audio integration
- Network multiplayer UI
