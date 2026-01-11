// Segment 5: Command Center - Boss Fight
// Turret boss arena - player aims from fixed positions.
// Final confrontation with the Station Commander.

const SEGMENT = #{
    id: "5_boss",
    name: "Command Center",

    // Game mode: turret (on-rails FPS)
    mode: "turret",
    path_id: "boss_path",

    // Play area bounds (large arena)
    bounds: #{
        min_x: -400.0, min_y: 0.0, min_z: -400.0,
        max_x: 400.0, max_y: 150.0, max_z: 250.0,
    },

    // Camera setup (follows turret path)
    camera: #{
        type: "perspective",
        fov: 90.0,
        follow_player: false,
    },

    // Background
    backgrounds: [
        #{ layer: "command_center", scroll_speed: 0.0, z: 0.0 },
    ],

    // No time limit - ends when boss defeated
    duration: 0,

    // No scroll
    scroll: #{
        enabled: false,
    },

    // Turret path - camera moves around the arena to different vantage points
    path: [
        #{ pos: #{ x: 0.0, y: 50.0, z: 200.0 }, rot: #{ yaw: 0.0, pitch: 0.0 }, t: 0.0 },
        #{ pos: #{ x: -200.0, y: 50.0, z: 100.0 }, rot: #{ yaw: 45.0, pitch: 0.0 }, t: 0.25 },
        #{ pos: #{ x: -200.0, y: 50.0, z: -100.0 }, rot: #{ yaw: 90.0, pitch: 0.0 }, t: 0.5 },
        #{ pos: #{ x: 200.0, y: 50.0, z: -100.0 }, rot: #{ yaw: -90.0, pitch: 0.0 }, t: 0.75 },
        #{ pos: #{ x: 0.0, y: 50.0, z: 200.0 }, rot: #{ yaw: 0.0, pitch: 0.0 }, t: 1.0 },
    ],

    // Boss identifier
    boss: "station_commander",

    // Arena geometry
    geometry: [
        // Arena floor (octagonal approximation)
        #{ type: "box", pos: #{ x: 0.0, y: 0.0, z: 0.0 }, size: #{ x: 700.0, y: 5.0, z: 500.0 }, color: #{ r: 70, g: 50, b: 50 } },
        // Ceiling with skylight
        #{ type: "box", pos: #{ x: 0.0, y: 150.0, z: 0.0 }, size: #{ x: 700.0, y: 5.0, z: 500.0 }, color: #{ r: 40, g: 30, b: 30 } },
        // Walls
        #{ type: "box", pos: #{ x: -347.0, y: 75.0, z: 0.0 }, size: #{ x: 6.0, y: 150.0, z: 500.0 }, color: #{ r: 50, g: 40, b: 40 } },
        #{ type: "box", pos: #{ x: 347.0, y: 75.0, z: 0.0 }, size: #{ x: 6.0, y: 150.0, z: 500.0 }, color: #{ r: 50, g: 40, b: 40 } },
        #{ type: "box", pos: #{ x: 0.0, y: 75.0, z: -247.0 }, size: #{ x: 700.0, y: 150.0, z: 6.0 }, color: #{ r: 50, g: 40, b: 40 } },
        #{ type: "box", pos: #{ x: 0.0, y: 75.0, z: 247.0 }, size: #{ x: 700.0, y: 150.0, z: 6.0 }, color: #{ r: 50, g: 40, b: 40 } },
        // Pillars for cover
        #{ type: "box", pos: #{ x: -250.0, y: 60.0, z: -150.0 }, size: #{ x: 40.0, y: 120.0, z: 40.0 }, color: #{ r: 80, g: 60, b: 60 } },
        #{ type: "box", pos: #{ x: 250.0, y: 60.0, z: -150.0 }, size: #{ x: 40.0, y: 120.0, z: 40.0 }, color: #{ r: 80, g: 60, b: 60 } },
        #{ type: "box", pos: #{ x: -250.0, y: 60.0, z: 100.0 }, size: #{ x: 40.0, y: 120.0, z: 40.0 }, color: #{ r: 80, g: 60, b: 60 } },
        #{ type: "box", pos: #{ x: 250.0, y: 60.0, z: 100.0 }, size: #{ x: 40.0, y: 120.0, z: 40.0 }, color: #{ r: 80, g: 60, b: 60 } },
        // Central platform (boss spawns here)
        #{ type: "box", pos: #{ x: 0.0, y: 10.0, z: -100.0 }, size: #{ x: 150.0, y: 20.0, z: 150.0 }, color: #{ r: 90, g: 70, b: 70 } },
        // Command throne
        #{ type: "box", pos: #{ x: 0.0, y: 50.0, z: -200.0 }, size: #{ x: 60.0, y: 80.0, z: 40.0 }, color: #{ r: 100, g: 50, b: 50 } },
    ],

    // Boss only - no regular spawns
    wave_pool: [],
    spawn_rate: 0.0,
    difficulty_curve: "flat",
};

fn get_segment() { SEGMENT }

fn on_enter(state) {
    // Boss intro
    // Spawn Station Commander at throne
    // Lock doors
}

fn on_tick(state, frame) {
    // Boss phases handled by boss script
    // Phase 1: Commander on platform, shooting
    // Phase 2: Commander mobile, spawns drones
    // Phase 3: Enraged, faster attacks

    // Boss AI updates happen here
    if frame == 90 {
        // Boss becomes active
    }
}

fn on_exit(state) {
    // Victory! Station Commander defeated
    // Trigger ending sequence
}
