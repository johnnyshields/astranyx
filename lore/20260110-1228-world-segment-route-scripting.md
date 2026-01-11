# World/Segment/Route Scripting System

## Overview

Implemented a comprehensive level structure system in Rhai for Astranyx. The system organizes gameplay into Worlds (stages), Segments (gameplay sections), and Routes (connections with triggers).

## Architecture

```
┌─────────────────────────────────────────────────────┐
│                  scripts/config.rhai                │
│              start_world: "station"                 │
└─────────────────────────┬───────────────────────────┘
                          │
┌─────────────────────────▼───────────────────────────┐
│           scripts/worlds/01_station/                │
│  ├── world.rhai         (start_segment, music)      │
│  ├── routes.rhai        (triggers, transitions)     │
│  └── segments/                                      │
│      ├── station_approach.rhai                      │
│      ├── station_interior.rhai                      │
│      └── station_hangar.rhai                        │
└─────────────────────────────────────────────────────┘
```

## Game Modes

Each segment declares one of these gameplay modes:

| Mode | Description | Camera | Player Control |
|------|-------------|--------|----------------|
| `side-scroll` | Classic shmup (R-Type/Gradius) | Fixed | 2D XY movement |
| `on-rails` | Starfox-style | Auto-follows path | Limited dodge |
| `free-flight` | Rogue Squadron-style | Chase camera | Full 3D, turnaround at bounds |
| `turret` | On-rails FPS | Auto-follows path | Aiming only |
| `first-person` | Full FPS | First person | WASD + mouse |

## Key Files

### Core Types (`crates/core/src/level/`)

- **`mod.rs`** - `LevelState`, `WorldDef`, `PendingChoice`, `CutsceneState`, `TransitionState`
- **`segment.rs`** - `GameMode`, `SegmentConfig`, `ScrollConfig`, `BackgroundLayer`, `DifficityCurve`
- **`camera.rs`** - `CameraConfig`, `CameraProjection`, `CameraState`
- **`route.rs`** - `Route`, `RouteTrigger`, `Transition`, `TransitionType`

### ScriptEngine Extensions (`crates/core/src/scripting/mod.rs`)

- `load_config_script_from_str()` - Load game config
- `load_world_script_from_str()` - Load world definitions
- `load_segment_script_from_str()` - Load segment definitions
- `load_route_script_from_str()` - Load route definitions
- `get_start_world()` - Get starting world from config
- `get_segment_config()` - Get segment config (bounds, camera, scroll, etc.)
- `get_routes_from()` - Get routes leaving a segment
- `call_segment_on_enter/tick/exit()` - Segment lifecycle callbacks

### Simulation Integration (`crates/core/src/simulation.rs`)

- `init_level_from_scripts()` - Initialize from config.rhai
- `update_level()` - Handle transitions, increment segment frame
- `update_scroll()` - Apply segment scroll config
- `check_route_triggers()` - Evaluate routes and start transitions

## Script Examples

### config.rhai
```rhai
const CONFIG = #{
    start_world: "station",
    tick_rate: 30,
    max_players: 4,
};
fn get_config() { CONFIG }
fn get_start_world() { CONFIG.start_world }
```

### world.rhai
```rhai
const WORLD = #{
    id: "station",
    name: "Space Station Alpha",
    start_segment: "station_approach",
    music: "stage1_theme",
};
fn get_world() { WORLD }
```

### segment.rhai
```rhai
const SEGMENT = #{
    id: "station_approach",
    name: "Approach Vector",
    mode: "side-scroll",
    bounds: #{ min_x: 0.0, min_y: 0.0, min_z: -100.0, max_x: 1920.0, max_y: 1080.0, max_z: 100.0 },
    camera: #{ type: "perspective", position: #{ x: 960.0, y: 540.0, z: 1000.0 }, fov: 60.0 },
    backgrounds: [ #{ layer: "stars_far", scroll_speed: 0.1, z: -500.0 } ],
    duration: 1800,
    scroll: #{ enabled: true, direction: #{ x: 1.0, y: 0.0, z: 0.0 }, speed: 60.0 },
    wave_pool: ["grunt", "shooter", "swerver"],
    spawn_rate: 1.0,
    difficulty_curve: "linear",
};
fn get_segment() { SEGMENT }
fn on_enter(state) { }
fn on_tick(state, frame) { }
fn on_exit(state) { }
```

### routes.rhai
```rhai
const ROUTES = [
    #{
        from: "station_approach",
        to: "station_interior",
        trigger: #{ type: "time", value: 1800 },
        transition: #{ type: "fade", duration: 30 },
    },
];
fn get_routes() { ROUTES }
```

## Route Triggers

| Type | Condition |
|------|-----------|
| `time` | `segment_frame >= value` |
| `distance` | `scroll_offset.x >= value` |
| `enemies_killed` | `enemies_killed >= value` |
| `boss_defeated` | `boss_defeated == true` |
| `bonus` | Custom condition (secret_path_found, no_damage, etc.) |
| `choice` | Player vote (not yet implemented) |
| `immediate` | Always true |

## Determinism

All level state is part of `GameState` and synced via lockstep:
- `LevelState.segment_id`, `segment_frame`, `scroll_offset`
- Route evaluation uses only synced state
- Transitions are deterministic (same trigger = same result)

## Client Integration

The client reads camera config from segments and updates on segment change:
```rust
simulation.init_level_from_scripts();
// Camera config comes from segment script
let camera_config = simulation.scripts.get_segment_config(&segment_id).camera;
```
