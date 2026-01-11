// Segment 4: Enemy Base - MGS-Style Maze
// Full FPS mode - WASD + mouse look with wall collisions.
// Navigate the maze, avoid/neutralize guards.

const SEGMENT = #{
    id: "4_base",
    name: "Enemy Base",

    // Game mode: full first-person with wall collision
    mode: "first-person",

    // Player starting position (entrance hallway)
    player_start: #{ x: 0.0, y: 1.7, z: 180.0 },

    // Play area bounds (expanded for maze)
    bounds: #{
        min_x: -200.0, min_y: 0.0, min_z: -300.0,
        max_x: 200.0, max_y: 50.0, max_z: 200.0,
    },

    // Camera setup (first person at player eye height)
    camera: #{
        type: "perspective",
        fov: 90.0,
        follow_player: true,
        follow_offset: #{ x: 0.0, y: 0.0, z: 0.0 },  // Eye position IS player position
    },

    // No scroll in FPS
    scroll: #{
        enabled: false,
    },

    // Duration: survive and clear enemies
    duration: 0,

    // ============================================
    // MAZE GEOMETRY - All walls are solid for collision
    // ============================================
    geometry: [
        // === FLOOR ===
        #{ type: "box", pos: #{ x: 0.0, y: -2.5, z: -50.0 }, size: #{ x: 400.0, y: 5.0, z: 500.0 },
           color: #{ r: 50, g: 50, b: 55 }, solid: false },

        // === CEILING ===
        #{ type: "box", pos: #{ x: 0.0, y: 47.5, z: -50.0 }, size: #{ x: 400.0, y: 5.0, z: 500.0 },
           color: #{ r: 40, g: 40, b: 45 }, solid: false },

        // === OUTER WALLS (solid) ===
        // North wall (back)
        #{ type: "box", pos: #{ x: 0.0, y: 22.5, z: -297.5 }, size: #{ x: 400.0, y: 45.0, z: 5.0 },
           color: #{ r: 60, g: 55, b: 65 }, solid: true },
        // South wall (front) - with entrance gap
        #{ type: "box", pos: #{ x: -100.0, y: 22.5, z: 197.5 }, size: #{ x: 200.0, y: 45.0, z: 5.0 },
           color: #{ r: 60, g: 55, b: 65 }, solid: true },
        #{ type: "box", pos: #{ x: 100.0, y: 22.5, z: 197.5 }, size: #{ x: 200.0, y: 45.0, z: 5.0 },
           color: #{ r: 60, g: 55, b: 65 }, solid: true },
        // West wall (left)
        #{ type: "box", pos: #{ x: -197.5, y: 22.5, z: -50.0 }, size: #{ x: 5.0, y: 45.0, z: 500.0 },
           color: #{ r: 55, g: 55, b: 60 }, solid: true },
        // East wall (right)
        #{ type: "box", pos: #{ x: 197.5, y: 22.5, z: -50.0 }, size: #{ x: 5.0, y: 45.0, z: 500.0 },
           color: #{ r: 55, g: 55, b: 60 }, solid: true },

        // === INTERIOR MAZE WALLS ===

        // Entry corridor walls (guide player forward)
        #{ type: "box", pos: #{ x: -40.0, y: 22.5, z: 120.0 }, size: #{ x: 5.0, y: 45.0, z: 150.0 },
           color: #{ r: 65, g: 60, b: 70 }, solid: true },
        #{ type: "box", pos: #{ x: 40.0, y: 22.5, z: 120.0 }, size: #{ x: 5.0, y: 45.0, z: 150.0 },
           color: #{ r: 65, g: 60, b: 70 }, solid: true },

        // First junction - T intersection
        #{ type: "box", pos: #{ x: 0.0, y: 22.5, z: 40.0 }, size: #{ x: 80.0, y: 45.0, z: 5.0 },
           color: #{ r: 65, g: 60, b: 70 }, solid: true },

        // Left branch corridor
        #{ type: "box", pos: #{ x: -120.0, y: 22.5, z: 0.0 }, size: #{ x: 5.0, y: 45.0, z: 80.0 },
           color: #{ r: 65, g: 60, b: 70 }, solid: true },
        #{ type: "box", pos: #{ x: -80.0, y: 22.5, z: -40.0 }, size: #{ x: 80.0, y: 45.0, z: 5.0 },
           color: #{ r: 65, g: 60, b: 70 }, solid: true },

        // Right branch corridor
        #{ type: "box", pos: #{ x: 120.0, y: 22.5, z: 0.0 }, size: #{ x: 5.0, y: 45.0, z: 80.0 },
           color: #{ r: 65, g: 60, b: 70 }, solid: true },
        #{ type: "box", pos: #{ x: 80.0, y: 22.5, z: -40.0 }, size: #{ x: 80.0, y: 45.0, z: 5.0 },
           color: #{ r: 65, g: 60, b: 70 }, solid: true },

        // Central room walls
        #{ type: "box", pos: #{ x: -60.0, y: 22.5, z: -100.0 }, size: #{ x: 5.0, y: 45.0, z: 120.0 },
           color: #{ r: 70, g: 65, b: 75 }, solid: true },
        #{ type: "box", pos: #{ x: 60.0, y: 22.5, z: -100.0 }, size: #{ x: 5.0, y: 45.0, z: 120.0 },
           color: #{ r: 70, g: 65, b: 75 }, solid: true },

        // Back room divider (with gaps)
        #{ type: "box", pos: #{ x: -100.0, y: 22.5, z: -180.0 }, size: #{ x: 80.0, y: 45.0, z: 5.0 },
           color: #{ r: 70, g: 65, b: 75 }, solid: true },
        #{ type: "box", pos: #{ x: 100.0, y: 22.5, z: -180.0 }, size: #{ x: 80.0, y: 45.0, z: 5.0 },
           color: #{ r: 70, g: 65, b: 75 }, solid: true },

        // === COVER OBJECTS ===

        // Crate near entrance (crouch behind)
        #{ type: "box", pos: #{ x: -70.0, y: 15.0, z: 80.0 }, size: #{ x: 30.0, y: 30.0, z: 30.0 },
           color: #{ r: 100, g: 80, b: 60 }, solid: true, tag: "cover" },

        // Server rack in left room
        #{ type: "box", pos: #{ x: -150.0, y: 22.5, z: -80.0 }, size: #{ x: 20.0, y: 45.0, z: 40.0 },
           color: #{ r: 30, g: 35, b: 40 }, solid: true, tag: "cover" },

        // Control console in right room
        #{ type: "box", pos: #{ x: 150.0, y: 15.0, z: -80.0 }, size: #{ x: 50.0, y: 30.0, z: 25.0 },
           color: #{ r: 35, g: 50, b: 60 }, solid: true, tag: "console" },

        // Central room pillar (cover)
        #{ type: "box", pos: #{ x: 0.0, y: 22.5, z: -120.0 }, size: #{ x: 20.0, y: 45.0, z: 20.0 },
           color: #{ r: 75, g: 70, b: 80 }, solid: true, tag: "pillar" },

        // Crates in back room
        #{ type: "box", pos: #{ x: -80.0, y: 12.5, z: -240.0 }, size: #{ x: 25.0, y: 25.0, z: 25.0 },
           color: #{ r: 90, g: 75, b: 55 }, solid: true, tag: "cover" },
        #{ type: "box", pos: #{ x: -80.0, y: 32.5, z: -240.0 }, size: #{ x: 20.0, y: 15.0, z: 20.0 },
           color: #{ r: 85, g: 70, b: 50 }, solid: true, tag: "cover" },
        #{ type: "box", pos: #{ x: 80.0, y: 12.5, z: -250.0 }, size: #{ x: 30.0, y: 25.0, z: 30.0 },
           color: #{ r: 95, g: 80, b: 60 }, solid: true, tag: "cover" },

        // === DECORATIVE (non-solid) ===

        // Light strips on ceiling (visual only)
        #{ type: "box", pos: #{ x: 0.0, y: 44.0, z: 100.0 }, size: #{ x: 60.0, y: 2.0, z: 3.0 },
           color: #{ r: 200, g: 200, b: 220 }, solid: false, tag: "light" },
        #{ type: "box", pos: #{ x: 0.0, y: 44.0, z: 0.0 }, size: #{ x: 60.0, y: 2.0, z: 3.0 },
           color: #{ r: 200, g: 200, b: 220 }, solid: false, tag: "light" },
        #{ type: "box", pos: #{ x: 0.0, y: 44.0, z: -100.0 }, size: #{ x: 100.0, y: 2.0, z: 3.0 },
           color: #{ r: 200, g: 200, b: 220 }, solid: false, tag: "light" },
        #{ type: "box", pos: #{ x: 0.0, y: 44.0, z: -220.0 }, size: #{ x: 150.0, y: 2.0, z: 3.0 },
           color: #{ r: 200, g: 200, b: 220 }, solid: false, tag: "light" },

        // Warning stripes near entrance
        #{ type: "box", pos: #{ x: 0.0, y: 0.1, z: 150.0 }, size: #{ x: 70.0, y: 0.2, z: 5.0 },
           color: #{ r: 200, g: 180, b: 50 }, solid: false },
    ],

    // === LIGHT SOURCES ===
    lights: [
        // Main overhead lights
        #{ type: "point", pos: #{ x: 0.0, y: 40.0, z: 100.0 }, color: #{ r: 255, g: 250, b: 240 }, intensity: 2.0, range: 80.0 },
        #{ type: "point", pos: #{ x: 0.0, y: 40.0, z: 0.0 }, color: #{ r: 255, g: 250, b: 240 }, intensity: 2.0, range: 80.0 },
        #{ type: "point", pos: #{ x: 0.0, y: 40.0, z: -100.0 }, color: #{ r: 255, g: 250, b: 240 }, intensity: 2.5, range: 100.0 },
        #{ type: "point", pos: #{ x: 0.0, y: 40.0, z: -220.0 }, color: #{ r: 255, g: 250, b: 240 }, intensity: 2.5, range: 120.0 },

        // Red warning light near back room
        #{ type: "point", pos: #{ x: -50.0, y: 35.0, z: -180.0 }, color: #{ r: 255, g: 100, b: 100 }, intensity: 1.0, range: 40.0 },

        // Blue console glow
        #{ type: "point", pos: #{ x: 150.0, y: 20.0, z: -80.0 }, color: #{ r: 100, g: 150, b: 255 }, intensity: 0.8, range: 30.0 },

        // Server rack green LED
        #{ type: "point", pos: #{ x: -150.0, y: 30.0, z: -80.0 }, color: #{ r: 100, g: 255, b: 100 }, intensity: 0.5, range: 20.0 },
    ],

    // === ENEMY CONFIGURATION ===
    wave_pool: ["grunt", "shooter", "sniper"],
    spawn_rate: 0.3,  // Lower rate - deliberate encounters
    difficulty_curve: "flat",  // Consistent difficulty
};

fn get_segment() { SEGMENT }

fn on_enter(state) {
    // FPS stealth mode activated
    // Spawn initial patrol guards
}

fn on_tick(state, frame) {
    // Guard patrol positions are handled by the simulation
    // Script can trigger events based on player position
}

fn on_exit(state) {
    // Base cleared - proceed to boss
}
