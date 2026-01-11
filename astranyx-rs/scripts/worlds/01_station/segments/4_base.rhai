// Segment 4: Enemy Base
// Full FPS mode - WASD + mouse look.
// Player explores the enemy command center.

const SEGMENT = #{
    id: "4_base",
    name: "Enemy Base",

    // Game mode: full first-person
    mode: "first-person",

    // Player starting position
    player_start: #{ x: 0.0, y: 5.0, z: 0.0 },

    // Play area bounds (interior room)
    bounds: #{
        min_x: -300.0, min_y: 0.0, min_z: -400.0,
        max_x: 300.0, max_y: 100.0, max_z: 50.0,
    },

    // Camera setup (first person at player eye height)
    camera: #{
        type: "perspective",
        fov: 90.0,
        follow_player: true,
        follow_offset: #{ x: 0.0, y: 1.7, z: 0.0 },  // Eye height
    },

    // Background layers (rendered as geometry)
    backgrounds: [
        #{ layer: "base_interior", scroll_speed: 0.0, z: 0.0 },
    ],

    // No time limit - ends via enemies_killed trigger
    duration: 0,

    // No scroll in FPS
    scroll: #{
        enabled: false,
    },

    // Room geometry
    geometry: [
        // Main room floor
        #{ type: "box", pos: #{ x: 0.0, y: 0.0, z: -175.0 }, size: #{ x: 600.0, y: 5.0, z: 400.0 }, color: #{ r: 60, g: 60, b: 70 } },
        // Ceiling
        #{ type: "box", pos: #{ x: 0.0, y: 100.0, z: -175.0 }, size: #{ x: 600.0, y: 5.0, z: 400.0 }, color: #{ r: 50, g: 50, b: 60 } },
        // Left wall
        #{ type: "box", pos: #{ x: -297.0, y: 50.0, z: -175.0 }, size: #{ x: 6.0, y: 100.0, z: 400.0 }, color: #{ r: 55, g: 55, b: 65 } },
        // Right wall
        #{ type: "box", pos: #{ x: 297.0, y: 50.0, z: -175.0 }, size: #{ x: 6.0, y: 100.0, z: 400.0 }, color: #{ r: 55, g: 55, b: 65 } },
        // Back wall
        #{ type: "box", pos: #{ x: 0.0, y: 50.0, z: -372.0 }, size: #{ x: 600.0, y: 100.0, z: 6.0 }, color: #{ r: 55, g: 55, b: 65 } },
        // Front wall with door opening
        #{ type: "box", pos: #{ x: -200.0, y: 50.0, z: 22.0 }, size: #{ x: 200.0, y: 100.0, z: 6.0 }, color: #{ r: 55, g: 55, b: 65 } },
        #{ type: "box", pos: #{ x: 200.0, y: 50.0, z: 22.0 }, size: #{ x: 200.0, y: 100.0, z: 6.0 }, color: #{ r: 55, g: 55, b: 65 } },
        // Cover: Crate
        #{ type: "box", pos: #{ x: -100.0, y: 25.0, z: -150.0 }, size: #{ x: 60.0, y: 50.0, z: 40.0 }, color: #{ r: 80, g: 70, b: 60 } },
        // Cover: Console
        #{ type: "box", pos: #{ x: 80.0, y: 40.0, z: -250.0 }, size: #{ x: 80.0, y: 80.0, z: 20.0 }, color: #{ r: 40, g: 60, b: 70 } },
        // Pillar 1
        #{ type: "box", pos: #{ x: -150.0, y: 50.0, z: -280.0 }, size: #{ x: 30.0, y: 100.0, z: 30.0 }, color: #{ r: 65, g: 65, b: 75 } },
        // Pillar 2
        #{ type: "box", pos: #{ x: 150.0, y: 50.0, z: -280.0 }, size: #{ x: 30.0, y: 100.0, z: 30.0 }, color: #{ r: 65, g: 65, b: 75 } },
    ],

    // FPS enemies
    wave_pool: ["shooter", "tank"],
    spawn_rate: 0.5,  // Lower rate - more deliberate encounters
    difficulty_curve: "stepped",
};

fn get_segment() { SEGMENT }

fn on_enter(state) {
    // FPS mode activated
    // Tutorial hint: WASD to move, mouse to aim
}

fn on_tick(state, frame) {
    // Initial enemies in the room
    if frame == 30 {
        // First shooter behind crate
    }

    if frame == 90 {
        // Second shooter at console
    }

    // Tank patrol enters at 10 seconds
    if frame == 300 {
        // Heavy enemy
    }

    // Reinforcements every 15 seconds
    if frame > 300 && frame % 450 == 0 {
        // Wave of shooters
    }
}

fn on_exit(state) {
    // Base cleared - proceed to boss
}
