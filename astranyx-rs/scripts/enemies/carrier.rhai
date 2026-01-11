// Carrier enemy - large, spawns mini-enemies
// High health, spawns grunts when shooting

const STATS = #{
    health: 120,
    speed: 25.0,
    points: 400,
    hitbox_radius: 40.0,
    fire_rate: 90,
    shoot_threshold: 60.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Slow steady movement
    let wave = sin(enemy.frame * 0.02) * 25.0;
    #{
        vx: -STATS.speed,
        vy: wave
    }
}

fn should_shoot(enemy) {
    let bounds = get_world_bounds();
    enemy.x < bounds.max_x - STATS.shoot_threshold
}

fn shoot(enemy) {
    // Spawn mini-enemies instead of bullets
    let offsets = [
        #{ x: 0.0, y: -30.0 },
        #{ x: 0.0, y: 30.0 },
        #{ x: 20.0, y: -15.0 },
        #{ x: 20.0, y: 15.0 },
    ];

    for offset in offsets {
        spawn_enemy("grunt", enemy.x + offset.x, enemy.y + offset.y);
    }
}
