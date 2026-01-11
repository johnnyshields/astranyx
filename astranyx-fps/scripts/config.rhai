// Game configuration
// Global settings and starting point for the game.

const CONFIG = #{
    // Starting world ID
    start_world: "station",

    // Game settings
    tick_rate: 30,          // Simulation ticks per second
    max_players: 4,         // Maximum players in a session

    // Default difficulty settings
    difficulty: #{
        enemy_health_multiplier: 1.0,
        enemy_damage_multiplier: 1.0,
        spawn_rate_multiplier: 1.0,
    },
};

fn get_config() { CONFIG }
fn get_start_world() { CONFIG.start_world }
