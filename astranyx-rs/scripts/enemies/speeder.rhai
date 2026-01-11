// Speeder enemy - very fast, low health
// Rushes across screen quickly

const STATS = #{
    health: 15,
    speed: 200.0,
    points: 60,
    hitbox_radius: 12.0,
    fire_rate: 120,
    shoot_threshold: 25.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Very fast straight movement with occasional dodge
    let dodge = 0.0;
    if enemy.frame % 60 < 10 {
        dodge = sin(enemy.frame * 0.5) * 150.0;
    }
    #{
        vx: -STATS.speed,
        vy: dodge
    }
}

fn should_shoot(enemy) {
    let bounds = get_world_bounds();
    enemy.x < bounds.max_x - STATS.shoot_threshold
}

fn shoot(enemy) {
    // Quick single shot
    spawn_bullet("enemy", enemy.x - 15.0, enemy.y, -400.0, 0.0, 5);
}
