// Weapon System - all 16 weapons across 4 ammo types
// Einhänder-style pickup system

// === BULLET WEAPONS (5) ===

const VULCAN = #{
    name: "Vulcan",
    display_name: "Vulcan",
    ammo_type: "BULLET",
    damage: 8,
    fire_rate: 3,
    ammo_per_pickup: 120,
    max_ammo: 400,
    speed: 500.0,
    count: 1,
    spread: 0.05,
    pierce: 0,
    lifetime: 180,
    special: "none",
};

const SHOTGUN = #{
    name: "shotgun",
    display_name: "Bulldog",
    ammo_type: "BULLET",
    damage: 6,
    fire_rate: 25,
    ammo_per_pickup: 30,
    max_ammo: 120,
    speed: 350.0,
    count: 8,
    spread: 0.5,
    pierce: 0,
    lifetime: 45,
    special: "none",
};

const SPREAD_SMALL = #{
    name: "spread_small",
    display_name: "Jericho",
    ammo_type: "BULLET",
    damage: 12,
    fire_rate: 12,
    ammo_per_pickup: 50,
    max_ammo: 200,
    speed: 400.0,
    count: 5,
    spread: 0.4,
    pierce: 0,
    lifetime: 150,
    special: "none",
};

const SPREAD_LARGE = #{
    name: "spread_large",
    display_name: "Kitsune",
    ammo_type: "BULLET",
    damage: 10,
    fire_rate: 15,
    ammo_per_pickup: 40,
    max_ammo: 150,
    speed: 380.0,
    count: 9,
    spread: 0.7,
    pierce: 0,
    lifetime: 150,
    special: "none",
};

const RAILGUN = #{
    name: "railgun",
    display_name: "Odin",
    ammo_type: "BULLET",
    damage: 80,
    fire_rate: 50,
    ammo_per_pickup: 12,
    max_ammo: 40,
    speed: 1200.0,
    count: 1,
    spread: 0.0,
    pierce: 10,
    lifetime: 60,
    special: "instant_hit",
};

// === BOMB WEAPONS (4) ===

const MISSILE = #{
    name: "missile",
    display_name: "Hornet",
    ammo_type: "BOMB",
    damage: 40,
    fire_rate: 18,
    ammo_per_pickup: 20,
    max_ammo: 80,
    speed: 180.0,
    count: 1,
    spread: 0.0,
    pierce: 0,
    lifetime: 300,
    special: "homing",
};

const CANNON = #{
    name: "cannon",
    display_name: "Megiddo",
    ammo_type: "BOMB",
    damage: 100,
    fire_rate: 45,
    ammo_per_pickup: 10,
    max_ammo: 35,
    speed: 300.0,
    count: 1,
    spread: 0.0,
    pierce: 0,
    lifetime: 180,
    special: "explosive",
};

const MINE = #{
    name: "mine",
    display_name: "Limpet",
    ammo_type: "BOMB",
    damage: 60,
    fire_rate: 40,
    ammo_per_pickup: 8,
    max_ammo: 20,
    speed: 50.0,
    count: 1,
    spread: 0.0,
    pierce: 0,
    lifetime: 600,
    special: "deployable",
};

const GRENADE = #{
    name: "grenade",
    display_name: "Magus",
    ammo_type: "BOMB",
    damage: 50,
    fire_rate: 30,
    ammo_per_pickup: 15,
    max_ammo: 50,
    speed: 280.0,
    count: 1,
    spread: 0.0,
    pierce: 0,
    lifetime: 120,
    special: "explosive",
};

// === OIL WEAPONS (2) ===

const FLAME = #{
    name: "flame",
    display_name: "Diablo",
    ammo_type: "OIL",
    damage: 3,
    fire_rate: 1,
    ammo_per_pickup: 250,
    max_ammo: 600,
    speed: 300.0,
    count: 3,
    spread: 0.2,
    pierce: 999,
    lifetime: 25,
    special: "continuous",
};

const ACID = #{
    name: "acid",
    display_name: "Slag",
    ammo_type: "OIL",
    damage: 25,
    fire_rate: 35,
    ammo_per_pickup: 25,
    max_ammo: 80,
    speed: 250.0,
    count: 1,
    spread: 0.0,
    pierce: 0,
    lifetime: 300,
    special: "puddle",
};

// === ENERGY WEAPONS (5) ===

const SONIC = #{
    name: "sonic",
    display_name: "Banshee",
    ammo_type: "ENERGY",
    damage: 30,
    fire_rate: 22,
    ammo_per_pickup: 35,
    max_ammo: 120,
    speed: 280.0,
    count: 1,
    spread: 0.0,
    pierce: 5,
    lifetime: 90,
    special: "wave",
};

const LASER_SMALL = #{
    name: "laser_small",
    display_name: "Lancet",
    ammo_type: "ENERGY",
    damage: 4,
    fire_rate: 1,
    ammo_per_pickup: 180,
    max_ammo: 500,
    speed: 0.0,
    count: 1,
    spread: 0.0,
    pierce: 999,
    lifetime: 1,
    special: "beam",
};

const LASER_LARGE = #{
    name: "laser_large",
    display_name: "Paladin",
    ammo_type: "ENERGY",
    damage: 10,
    fire_rate: 1,
    ammo_per_pickup: 120,
    max_ammo: 350,
    speed: 0.0,
    count: 1,
    spread: 0.0,
    pierce: 999,
    lifetime: 1,
    special: "beam_wide",
};

const LIGHTNING = #{
    name: "lightning",
    display_name: "Valkyrie",
    ammo_type: "ENERGY",
    damage: 35,
    fire_rate: 18,
    ammo_per_pickup: 25,
    max_ammo: 90,
    speed: 600.0,
    count: 1,
    spread: 0.0,
    pierce: 0,
    lifetime: 20,
    special: "chain",
};

const SWORD = #{
    name: "sword",
    display_name: "Durandal",
    ammo_type: "ENERGY",
    damage: 120,
    fire_rate: 28,
    ammo_per_pickup: 12,
    max_ammo: 35,
    speed: 0.0,
    count: 1,
    spread: 0.0,
    pierce: 999,
    lifetime: 10,
    special: "melee",
};

// All weapons map
const WEAPONS = #{
    vulcan: VULCAN,
    shotgun: SHOTGUN,
    spread_small: SPREAD_SMALL,
    spread_large: SPREAD_LARGE,
    railgun: RAILGUN,
    missile: MISSILE,
    cannon: CANNON,
    mine: MINE,
    grenade: GRENADE,
    flame: FLAME,
    acid: ACID,
    sonic: SONIC,
    laser_small: LASER_SMALL,
    laser_large: LASER_LARGE,
    lightning: LIGHTNING,
    sword: SWORD,
};

// Get weapon stats by name
fn get_weapon(name) {
    WEAPONS[name]
}

// Get all weapon names
fn get_all_weapons() {
    ["vulcan", "shotgun", "spread_small", "spread_large", "railgun",
     "missile", "cannon", "mine", "grenade",
     "flame", "acid",
     "sonic", "laser_small", "laser_large", "lightning", "sword"]
}

// Get weapons available at a given wave
fn get_available_weapons(wave) {
    let weapons = ["vulcan", "shotgun", "spread_small"];

    if wave >= 3 {
        weapons += "missile";
        weapons += "flame";
    }
    if wave >= 5 {
        weapons += "spread_large";
        weapons += "cannon";
        weapons += "sonic";
    }
    if wave >= 7 {
        weapons += "grenade";
        weapons += "acid";
        weapons += "laser_small";
    }
    if wave >= 9 {
        weapons += "lightning";
        weapons += "laser_large";
    }
    if wave >= 12 {
        weapons += "railgun";
        weapons += "mine";
        weapons += "sword";
    }

    weapons
}

// Get weapons by ammo type
fn get_weapons_by_ammo_type(ammo_type) {
    let result = [];
    let all = get_all_weapons();

    for name in all {
        let weapon = WEAPONS[name];
        if weapon.ammo_type == ammo_type {
            result += name;
        }
    }

    result
}

// Fire weapon - returns projectile spawn data
fn fire_weapon(weapon_name, player_x, player_y, aim_angle) {
    let weapon = WEAPONS[weapon_name];
    let projectiles = [];

    // Calculate spread angles
    let half_spread = weapon.spread / 2.0;
    let angle_step = if weapon.count > 1 {
        weapon.spread / (weapon.count - 1)
    } else {
        0.0
    };

    for i in range(0, weapon.count) {
        let angle = aim_angle;
        if weapon.count > 1 {
            angle = aim_angle - half_spread + i * angle_step;
        } else if weapon.spread > 0.0 {
            // Single projectile with random spread
            let rng = get_random();
            angle = aim_angle + (rng - 0.5) * weapon.spread;
        }

        let vx = cos(angle) * weapon.speed;
        let vy = sin(angle) * weapon.speed;

        projectiles += #{
            x: player_x + 20.0,
            y: player_y,
            vx: vx,
            vy: vy,
            damage: weapon.damage,
            pierce: weapon.pierce,
            lifetime: weapon.lifetime,
            special: weapon.special,
        };
    }

    projectiles
}

// Check if weapon is continuous fire type
fn is_continuous_fire(weapon_name) {
    let weapon = WEAPONS[weapon_name];
    weapon.special == "continuous" || weapon.special == "beam" || weapon.special == "beam_wide"
}

// Get bullet visual type for rendering
fn get_bullet_type(weapon_name) {
    let specials = #{
        "instant_hit": "laser",
        "homing": "missile",
        "explosive": "big",
        "continuous": "flame",
        "puddle": "acid",
        "wave": "ring",
        "beam": "laser",
        "beam_wide": "laser",
        "chain": "laser",
        "melee": "shot",
    };

    let weapon = WEAPONS[weapon_name];
    if specials.contains(weapon.special) {
        specials[weapon.special]
    } else {
        if weapon.ammo_type == "BULLET" {
            if weapon.count > 1 { "spread" } else { "shot" }
        } else {
            "shot"
        }
    }
}

// Ammo type colors (RGBA)
fn get_ammo_color(ammo_type) {
    if ammo_type == "BULLET" { #{ r: 1.0, g: 0.85, b: 0.2, a: 1.0 } }
    else if ammo_type == "BOMB" { #{ r: 1.0, g: 0.4, b: 0.1, a: 1.0 } }
    else if ammo_type == "OIL" { #{ r: 0.4, g: 0.9, b: 0.2, a: 1.0 } }
    else { #{ r: 0.3, g: 0.7, b: 1.0, a: 1.0 } } // ENERGY
}
