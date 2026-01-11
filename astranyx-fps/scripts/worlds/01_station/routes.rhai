// Route Definitions for Station World
// Connects segments together with triggers and transitions.
// Flow: Approach -> Corridor -> Hangar -> Base -> Boss -> Victory

const ROUTES = [
    // 1. Approach -> Corridor (kill 15 enemies)
    #{
        from: "1_approach",
        to: "2_corridor",
        trigger: #{
            type: "enemies_killed",
            value: 15,
        },
        transition: #{
            type: "fade",
            duration: 45,
        },
        priority: 0,
    },

    // 2. Corridor -> Hangar (kill 20 enemies)
    #{
        from: "2_corridor",
        to: "3_hangar",
        trigger: #{
            type: "enemies_killed",
            value: 20,
        },
        transition: #{
            type: "fade",
            duration: 60,
        },
        priority: 0,
    },

    // 3. Hangar -> Base (kill 15 enemies)
    #{
        from: "3_hangar",
        to: "4_base",
        trigger: #{
            type: "enemies_killed",
            value: 15,
        },
        transition: #{
            type: "fade",
            duration: 60,
        },
        priority: 0,
    },

    // 4. Base -> Boss (kill 25 enemies)
    #{
        from: "4_base",
        to: "5_boss",
        trigger: #{
            type: "enemies_killed",
            value: 25,
        },
        transition: #{
            type: "fade",
            duration: 45,
        },
        priority: 0,
    },

    // 5. Boss -> Victory (after boss defeated)
    #{
        from: "5_boss",
        to: "victory",
        trigger: #{
            type: "boss_defeated",
        },
        transition: #{
            type: "fade",
            duration: 90,  // Long fade for ending
        },
        priority: 0,
    },

    // Secret route: Approach -> Secret area (if all enemies killed before time limit)
    #{
        from: "1_approach",
        to: "secret_area",
        trigger: #{
            type: "bonus",
            condition: "all_enemies_killed",
        },
        transition: #{
            type: "wipe",
            duration: 30,
        },
        priority: 10,  // Higher priority than normal time-based route
    },
];

fn get_routes() { ROUTES }

// Get routes from a specific segment
fn get_routes_from(segment_id) {
    let results = [];
    for route in ROUTES {
        if route.from == segment_id {
            results += route;
        }
    }
    // Sort by priority (higher first)
    results.sort(|a, b| b.priority - a.priority);
    results
}

// Evaluate a trigger condition
fn evaluate_trigger(trigger, state) {
    let trigger_type = trigger.type;

    if trigger_type == "distance" {
        return state.scroll_offset >= trigger.value;
    }

    if trigger_type == "time" {
        return state.segment_frame >= trigger.value;
    }

    if trigger_type == "enemies_killed" {
        return state.enemies_killed >= trigger.value;
    }

    if trigger_type == "boss_defeated" {
        return state.boss_defeated;
    }

    if trigger_type == "bonus" {
        return evaluate_condition(trigger.condition, state);
    }

    if trigger_type == "immediate" {
        return true;
    }

    false
}

// Evaluate a custom condition
fn evaluate_condition(condition, state) {
    if condition == "secret_path_found" {
        return state.secrets_found > 0;
    }

    if condition == "all_enemies_killed" {
        return state.enemies_spawned > 0 && state.enemies_spawned == state.enemies_killed;
    }

    if condition == "no_damage" {
        return state.damage_taken == 0;
    }

    false
}
