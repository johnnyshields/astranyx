// Powerup System - 11 powerup types with weighted random selection
// Effects applied to player on pickup

// Powerup definitions with rarity weights
const POWERUPS = #{
    SHIELD: #{
        name: "SHIELD",
        description: "Restore shields",
        color_index: 0,
        rarity: 0.2,
        effect: "add_shields",
        value: 35,
        max_stacks: 1,
    },
    UPGRADE: #{
        name: "UPGRADE",
        description: "Upgrade ship",
        color_index: 1,
        rarity: 0.1,
        effect: "upgrade_ship",
        value: 1,
        max_stacks: 3,
    },
    SPREAD: #{
        name: "SPREAD",
        description: "Spread shot",
        color_index: 2,
        rarity: 0.15,
        effect: "add_stat",
        stat: "spread",
        value: 1,
        max_stacks: 3,
    },
    LASER: #{
        name: "LASER",
        description: "Laser power",
        color_index: 3,
        rarity: 0.15,
        effect: "add_stat",
        stat: "laser",
        value: 1,
        max_stacks: 3,
    },
    MISSILE: #{
        name: "MISSILE",
        description: "Homing missiles",
        color_index: 4,
        rarity: 0.1,
        effect: "add_stat",
        stat: "missile",
        value: 1,
        max_stacks: 3,
    },
    ORBIT: #{
        name: "ORBIT",
        description: "Orbital shield",
        color_index: 5,
        rarity: 0.1,
        effect: "add_orb",
        value: 1,
        max_stacks: 6,
    },
    DRONE: #{
        name: "DRONE",
        description: "Attack drone",
        color_index: 6,
        rarity: 0.1,
        effect: "add_drone",
        value: 1,
        max_stacks: 4,
    },
    SPEED: #{
        name: "SPEED",
        description: "Speed boost",
        color_index: 7,
        rarity: 0.2,
        effect: "add_stat",
        stat: "speed",
        value: 1,
        max_stacks: 3,
    },
    RAPID: #{
        name: "RAPID",
        description: "Rapid fire",
        color_index: 8,
        rarity: 0.15,
        effect: "add_stat",
        stat: "rapid",
        value: 1,
        max_stacks: 3,
    },
    PIERCE: #{
        name: "PIERCE",
        description: "Piercing shots",
        color_index: 9,
        rarity: 0.1,
        effect: "add_stat",
        stat: "pierce",
        value: 1,
        max_stacks: 2,
    },
    LIFE: #{
        name: "LIFE",
        description: "Extra life",
        color_index: 10,
        rarity: 0.05,
        effect: "add_life",
        value: 1,
        max_stacks: 99,
    },
};

// All powerup types
const ALL_POWERUP_TYPES = [
    "SHIELD", "UPGRADE", "SPREAD", "LASER", "MISSILE",
    "ORBIT", "DRONE", "SPEED", "RAPID", "PIERCE", "LIFE"
];

// Get powerup by name
fn get_powerup(name) {
    POWERUPS[name]
}

// Get all powerup types
fn get_all_powerups() {
    ALL_POWERUP_TYPES
}

// Get random powerup type based on rarity weights
fn get_random_powerup(rng) {
    // Calculate total weight
    let total_weight = 0.0;
    for ptype in ALL_POWERUP_TYPES {
        total_weight += POWERUPS[ptype].rarity;
    }

    // Pick based on weighted random
    let roll = rng * total_weight;
    let cumulative = 0.0;

    for ptype in ALL_POWERUP_TYPES {
        cumulative += POWERUPS[ptype].rarity;
        if roll <= cumulative {
            return ptype;
        }
    }

    "SHIELD" // Fallback
}

// Apply powerup effect to player
fn apply_powerup(player_id, powerup_type) {
    let data = POWERUPS[powerup_type];

    if data.effect == "add_shields" {
        add_player_shields(player_id, data.value);
    } else if data.effect == "upgrade_ship" {
        upgrade_player_ship(player_id);
    } else if data.effect == "add_stat" {
        add_player_stat(player_id, data.stat, data.value, data.max_stacks);
    } else if data.effect == "add_orb" {
        add_player_orb(player_id, data.max_stacks);
    } else if data.effect == "add_drone" {
        add_player_drone(player_id, data.max_stacks);
    } else if data.effect == "add_life" {
        add_player_life(player_id);
    }
}

// Check if powerup type is a weapon powerup
fn is_weapon_powerup(powerup_type) {
    powerup_type == "SPREAD" || powerup_type == "LASER" || powerup_type == "MISSILE"
}

// Check if powerup type is a stat powerup
fn is_stat_powerup(powerup_type) {
    powerup_type == "SPEED" || powerup_type == "RAPID" || powerup_type == "PIERCE"
}

// Check if powerup type is a special powerup
fn is_special_powerup(powerup_type) {
    powerup_type == "SHIELD" || powerup_type == "UPGRADE" ||
    powerup_type == "LIFE" || powerup_type == "ORBIT" || powerup_type == "DRONE"
}

// Get powerup color for rendering (RGBA)
fn get_powerup_color(powerup_type) {
    let colors = [
        #{ r: 0.3, g: 0.7, b: 1.0, a: 1.0 },   // SHIELD - blue
        #{ r: 1.0, g: 0.85, b: 0.2, a: 1.0 },  // UPGRADE - gold
        #{ r: 1.0, g: 0.5, b: 0.2, a: 1.0 },   // SPREAD - orange
        #{ r: 0.2, g: 1.0, b: 1.0, a: 1.0 },   // LASER - cyan
        #{ r: 1.0, g: 0.3, b: 0.3, a: 1.0 },   // MISSILE - red
        #{ r: 0.8, g: 0.4, b: 1.0, a: 1.0 },   // ORBIT - purple
        #{ r: 0.4, g: 1.0, b: 0.4, a: 1.0 },   // DRONE - green
        #{ r: 1.0, g: 1.0, b: 0.4, a: 1.0 },   // SPEED - yellow
        #{ r: 1.0, g: 0.6, b: 0.8, a: 1.0 },   // RAPID - pink
        #{ r: 0.6, g: 0.6, b: 1.0, a: 1.0 },   // PIERCE - light blue
        #{ r: 1.0, g: 0.2, b: 0.5, a: 1.0 },   // LIFE - magenta
    ];

    let data = POWERUPS[powerup_type];
    colors[data.color_index]
}

// Get drop chance for enemy type
fn get_drop_chance(enemy_type) {
    // Base drop chances by enemy type
    let chances = #{
        grunt: 0.05,
        shooter: 0.08,
        swerver: 0.06,
        tank: 0.15,
        speeder: 0.04,
        bomber: 0.12,
        sniper: 0.10,
        carrier: 0.20,
        mine: 0.03,
        spiral: 0.10,
        shield: 0.12,
        splitter: 0.08,
    };

    if chances.contains(enemy_type) {
        chances[enemy_type]
    } else {
        0.05
    }
}

// Should enemy drop a powerup?
fn should_drop_powerup(enemy_type, rng) {
    let chance = get_drop_chance(enemy_type);
    rng < chance
}

// Powerup physics
const POWERUP_DRIFT_SPEED = -30.0;  // Slow leftward drift
const POWERUP_BOB_SPEED = 0.1;       // Vertical bob animation speed
const POWERUP_BOB_AMPLITUDE = 5.0;   // Vertical bob distance
const POWERUP_LIFETIME = 600;        // 10 seconds at 60fps
const POWERUP_BLINK_START = 120;     // Start blinking at 2 seconds remaining
const POWERUP_HITBOX_RADIUS = 15.0;

fn get_powerup_velocity() {
    #{ vx: POWERUP_DRIFT_SPEED, vy: 0.0 }
}

fn get_powerup_bob_offset(frame) {
    sin(frame * POWERUP_BOB_SPEED) * POWERUP_BOB_AMPLITUDE
}

fn get_powerup_opacity(lifetime) {
    if lifetime > POWERUP_BLINK_START {
        1.0
    } else {
        // Blink faster as expiration approaches
        if lifetime % 10 < 5 { 1.0 } else { 0.3 }
    }
}
