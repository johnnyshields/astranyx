// Segment 3: Hangar Bay
// FPS turret section - player aims with crosshair while camera follows path.
// Defense turret section as player craft docks.

const SEGMENT = #{
    id: "3_hangar",
    name: "Hangar Bay",

    // Game mode: turret (FPS on-rails)
    mode: "turret",
    path_id: "hangar_path",

    // Play area bounds (hangar interior)
    bounds: #{
        min_x: -500.0, min_y: 0.0, min_z: -800.0,
        max_x: 500.0, max_y: 200.0, max_z: 100.0,
    },

    // Camera setup (follows path, player aims independently)
    camera: #{
        type: "perspective",
        fov: 75.0,
        follow_player: false,
    },

    // Background layers
    backgrounds: [
        #{ layer: "hangar_interior", scroll_speed: 0.0, z: 0.0 },
    ],

    // Segment duration
    duration: 900,  // 30 seconds

    // No scroll (on rails)
    scroll: #{
        enabled: false,
    },

    // Turret path through hangar
    path: [
        #{ pos: #{ x: 0.0, y: 50.0, z: 0.0 }, rot: #{ yaw: 0.0, pitch: 0.0 }, t: 0.0 },
        #{ pos: #{ x: 100.0, y: 50.0, z: -200.0 }, rot: #{ yaw: 20.0, pitch: 0.0 }, t: 0.3 },
        #{ pos: #{ x: 0.0, y: 50.0, z: -400.0 }, rot: #{ yaw: 0.0, pitch: 10.0 }, t: 0.6 },
        #{ pos: #{ x: -50.0, y: 50.0, z: -600.0 }, rot: #{ yaw: -15.0, pitch: 0.0 }, t: 1.0 },
    ],

    // Hangar geometry (placeholder boxes)
    geometry: [
        // Floor
        #{ type: "box", pos: #{ x: 0.0, y: 0.0, z: -300.0 }, size: #{ x: 800.0, y: 10.0, z: 800.0 }, color: #{ r: 70, g: 70, b: 80 } },
        // Crate
        #{ type: "box", pos: #{ x: -200.0, y: 50.0, z: -100.0 }, size: #{ x: 40.0, y: 80.0, z: 40.0 }, color: #{ r: 100, g: 80, b: 50 } },
        // Parked ship
        #{ type: "box", pos: #{ x: 150.0, y: 40.0, z: -300.0 }, size: #{ x: 60.0, y: 60.0, z: 100.0 }, color: #{ r: 80, g: 80, b: 90 } },
        // Control tower
        #{ type: "box", pos: #{ x: -300.0, y: 80.0, z: -500.0 }, size: #{ x: 50.0, y: 160.0, z: 50.0 }, color: #{ r: 60, g: 70, b: 80 } },
        // Hangar door frame
        #{ type: "box", pos: #{ x: 0.0, y: 100.0, z: -700.0 }, size: #{ x: 300.0, y: 200.0, z: 20.0 }, color: #{ r: 50, g: 50, b: 60 } },
    ],

    // FPS enemies (snipers and shooters)
    wave_pool: ["shooter", "sniper"],
    spawn_rate: 1.5,
    difficulty_curve: "linear",
};

fn get_segment() { SEGMENT }

fn on_enter(state) {
    // Turret mode activated
    // Show crosshair
}

fn on_tick(state, frame) {
    // Enemies pop up from cover
    if frame == 60 {
        // First shooter behind crate
    }

    if frame == 180 {
        // Sniper on control tower
    }

    if frame == 450 {
        // Multiple enemies from ship
    }

    // Random spawns throughout
    if frame > 200 && frame % 90 == 0 {
        // Pop-up enemies
    }
}

fn on_exit(state) {
    // Hangar secured
}
