// Wave spawning system - controls enemy waves and boss spawns
// Matches JS version progression

// Get available enemy types for a wave
fn get_available_enemies(wave) {
    let enemies = ["grunt"];

    if wave >= 2 { enemies += "swerver"; }
    if wave >= 3 { enemies += "shooter"; enemies += "speeder"; }
    if wave >= 4 { enemies += "mine"; }
    if wave >= 5 { enemies += "bomber"; enemies += "spiral"; }
    if wave >= 7 { enemies += "tank"; enemies += "sniper"; }
    if wave >= 9 { enemies += "carrier"; enemies += "shield"; }
    if wave >= 11 { enemies += "splitter"; }

    enemies
}

// Get number of enemies for a wave
fn get_enemy_count(wave) {
    let base = 4;
    let scaling = floor(wave * 0.8);
    base + scaling
}

// Check if boss should spawn this wave
fn should_spawn_boss(wave) {
    wave > 0 && wave % 5 == 0
}

// Get boss type for a wave (0-5)
fn get_boss_type(wave) {
    let boss_num = (wave / 5) - 1;
    min(boss_num, 5)
}

// Get spawn pattern for a wave
fn get_spawn_pattern(wave, rng) {
    let patterns = ["line", "v_formation", "swarm", "mixed", "rush", "surround"];
    let idx = floor(rng * len(patterns));
    patterns[idx]
}

// Generate spawn positions for a pattern
fn generate_spawns(pattern, count, bounds, rng) {
    let spawns = [];
    let start_x = bounds.max_x + 50.0;

    if pattern == "line" {
        // Horizontal line formation
        let y_start = bounds.min_y + 100.0;
        let y_range = bounds.max_y - bounds.min_y - 200.0;
        let y_step = y_range / count;

        for i in range(0, count) {
            spawns += #{
                x: start_x + i * 30.0,
                y: y_start + i * y_step
            };
        }
    } else if pattern == "v_formation" {
        // V-shaped formation
        let center_y = (bounds.min_y + bounds.max_y) / 2.0;

        for i in range(0, count) {
            let offset = (i - count / 2) * 60.0;
            let x_offset = abs(offset) * 0.5;
            spawns += #{
                x: start_x + x_offset,
                y: center_y + offset
            };
        }
    } else if pattern == "swarm" {
        // Random scattered formation
        for i in range(0, count) {
            spawns += #{
                x: start_x + rng * 200.0,
                y: bounds.min_y + 100.0 + rng * (bounds.max_y - bounds.min_y - 200.0)
            };
        }
    } else if pattern == "mixed" {
        // Shooters on edges, grunts in center
        let y_step = (bounds.max_y - bounds.min_y - 200.0) / count;

        for i in range(0, count) {
            let y = bounds.min_y + 100.0 + i * y_step;
            spawns += #{
                x: start_x + (i % 3) * 40.0,
                y: y
            };
        }
    } else if pattern == "rush" {
        // All enemies spawn close together
        let center_y = (bounds.min_y + bounds.max_y) / 2.0;

        for i in range(0, count) {
            let offset_y = (i - count / 2) * 40.0;
            spawns += #{
                x: start_x + (i % 2) * 20.0,
                y: center_y + offset_y
            };
        }
    } else {
        // "surround" - vertical line
        let y_step = (bounds.max_y - bounds.min_y - 100.0) / count;

        for i in range(0, count) {
            spawns += #{
                x: start_x,
                y: bounds.min_y + 50.0 + i * y_step
            };
        }
    }

    spawns
}

// Pick random enemy type from available ones
fn pick_enemy_type(available, rng) {
    let idx = floor(rng * len(available));
    available[idx]
}

// Get wave difficulty multiplier
fn get_difficulty_multiplier(wave) {
    1.0 + wave * 0.1
}

// Get time between waves in seconds
fn get_wave_delay(wave) {
    if wave == 0 {
        1.2  // First wave delay
    } else {
        6.0  // Normal delay
    }
}

// Should spawn heavy enemies this wave?
fn should_spawn_heavy(wave, rng) {
    wave >= 5 && rng > 0.7
}
