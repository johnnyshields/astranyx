// Segment 2: Station Corridor
// On-rails shmup section (Starfox-style).
// Camera follows a path through the station corridor.

const SEGMENT = #{
    id: "2_corridor",
    name: "Station Corridor",

    // Game mode: on-rails camera following a path
    mode: "on-rails",
    path_id: "corridor_path",

    // Play area bounds (3D corridor)
    bounds: #{
        min_x: -200.0, min_y: 0.0, min_z: -2000.0,
        max_x: 700.0, max_y: 300.0, max_z: 100.0,
    },

    // Camera setup (follows path)
    camera: #{
        type: "perspective",
        fov: 70.0,
        follow_player: false,
    },

    // Background layers (corridor walls rendered as geometry)
    backgrounds: [
        #{ layer: "corridor_interior", scroll_speed: 0.0, z: 0.0 },
    ],

    // Segment duration (frames at 30Hz)
    duration: 1200,  // 40 seconds

    // No scroll (camera on rails)
    scroll: #{
        enabled: false,
    },

    // Path definition for on-rails movement
    path: [
        #{ pos: #{ x: 0.0, y: 100.0, z: 0.0 }, rot: #{ yaw: 0.0, pitch: 0.0 }, t: 0.0 },
        #{ pos: #{ x: 200.0, y: 100.0, z: -400.0 }, rot: #{ yaw: 0.0, pitch: 0.0 }, t: 0.25 },
        #{ pos: #{ x: 400.0, y: 120.0, z: -800.0 }, rot: #{ yaw: 15.0, pitch: -5.0 }, t: 0.5 },
        #{ pos: #{ x: 300.0, y: 100.0, z: -1200.0 }, rot: #{ yaw: -10.0, pitch: 0.0 }, t: 0.75 },
        #{ pos: #{ x: 500.0, y: 100.0, z: -1600.0 }, rot: #{ yaw: 0.0, pitch: 0.0 }, t: 1.0 },
    ],

    // Placeholder geometry for corridor
    geometry: [
        // Floor
        #{ type: "box", pos: #{ x: 0.0, y: 0.0, z: -800.0 }, size: #{ x: 600.0, y: 10.0, z: 1600.0 }, color: #{ r: 60, g: 60, b: 70 } },
        // Left wall
        #{ type: "box", pos: #{ x: -290.0, y: 150.0, z: -800.0 }, size: #{ x: 20.0, y: 300.0, z: 1600.0 }, color: #{ r: 50, g: 50, b: 60 } },
        // Right wall
        #{ type: "box", pos: #{ x: 590.0, y: 150.0, z: -800.0 }, size: #{ x: 20.0, y: 300.0, z: 1600.0 }, color: #{ r: 50, g: 50, b: 60 } },
        // Ceiling
        #{ type: "box", pos: #{ x: 0.0, y: 300.0, z: -800.0 }, size: #{ x: 600.0, y: 10.0, z: 1600.0 }, color: #{ r: 40, g: 40, b: 50 } },
    ],

    // More challenging enemies for mid-section
    wave_pool: ["shooter", "swerver", "tank"],
    spawn_rate: 0.8,
    difficulty_curve: "exponential",
};

fn get_segment() { SEGMENT }

fn on_enter(state) {
    // Entering corridor - tighter quarters
}

fn on_tick(state, frame) {
    // Spawn enemies ahead on the path
    if frame == 150 {
        // Shooters at corridor entrance
    }

    if frame == 450 {
        // Mid-corridor ambush
    }

    // Tank appears at 2/3 through
    if frame == 800 {
        // Heavy enemy blocks path
    }
}

fn on_exit(state) {
    // Corridor cleared
}
