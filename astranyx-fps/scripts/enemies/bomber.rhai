// Bomber enemy - drops bombs downward
// Moderate health, dangerous to players below

const STATS = #{
    health: 60,
    speed: 40.0,
    points: 150,
    hitbox_radius: 22.0,
    fire_rate: 50,
    shoot_threshold: 35.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Slow descent pattern
    let wave_x = sin(enemy.frame * 0.04) * 10.0;
    #{
        vx: -STATS.speed + wave_x,
        vy: sin(enemy.frame * 0.02) * 30.0
    }
}

fn should_shoot(enemy) {
    let bounds = get_world_bounds();
    enemy.x < bounds.max_x - STATS.shoot_threshold
}

fn shoot(enemy) {
    // Drop bombs downward
    spawn_bullet("bomb", enemy.x, enemy.y + 20.0, -50.0, 200.0, 15);
    // Occasional second bomb
    if get_random() > 0.5 {
        spawn_bullet("bomb", enemy.x - 20.0, enemy.y + 20.0, -30.0, 180.0, 15);
    }
}
