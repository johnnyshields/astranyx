// Segment 1: Station Approach
// Classic horizontal scrolling shmup section.
// Opening segment - players approach the enemy space station.

const SEGMENT = #{
    id: "1_approach",
    name: "Approach Vector",

    // Game mode: classic side-scrolling shmup
    mode: "side-scroll",

    // Play area bounds
    bounds: #{
        min_x: 0.0, min_y: 0.0, min_z: -100.0,
        max_x: 1920.0, max_y: 1080.0, max_z: 100.0,
    },

    // Camera setup
    camera: #{
        type: "perspective",
        position: #{ x: 960.0, y: 540.0, z: 1000.0 },
        target: #{ x: 960.0, y: 540.0, z: 0.0 },
        fov: 60.0,
        follow_player: false,
    },

    // Background layers (parallax scrolling)
    backgrounds: [
        #{ layer: "stars_far", scroll_speed: 0.1, z: -500.0 },
        #{ layer: "nebula", scroll_speed: 0.3, z: -300.0 },
        #{ layer: "station_silhouette", scroll_speed: 0.6, z: -100.0 },
    ],

    // Segment length (frames at 30Hz)
    duration: 1800,  // 60 seconds

    // Scroll behavior
    scroll: #{
        enabled: true,
        direction: #{ x: 1.0, y: 0.0, z: 0.0 },
        speed: 60.0,  // pixels per second
    },

    // Enemy waves for this segment
    wave_pool: ["grunt", "shooter", "swerver"],
    spawn_rate: 1.0,
    difficulty_curve: "linear",
};

fn get_segment() { SEGMENT }

// Called when segment starts
fn on_enter(state) {
    // Initial wave announcement
}

// Called each frame - custom spawning logic
fn on_tick(state, frame) {
    // Spawn patterns based on frame
    if frame == 90 {
        // First wave at 3 seconds
    }

    if frame == 300 {
        // Second wave at 10 seconds - shooters in V formation
    }

    if frame == 600 {
        // Third wave at 20 seconds - swervers
    }

    // Random spawns after initial waves
    if frame > 600 && frame % 150 == 0 {
        // Mixed enemy waves
    }
}

// Called when segment ends
fn on_exit(state) {
    // Transition to corridor
}
