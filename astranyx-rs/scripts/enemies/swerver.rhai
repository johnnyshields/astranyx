// Swerver enemy - fast with large sine wave movement
// Hard to hit due to erratic movement

const STATS = #{
    health: 25,
    speed: 100.0,
    points: 75,
    hitbox_radius: 14.0,
    fire_rate: 120,
    shoot_threshold: 18.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Fast sine wave - harder to predict
    let wave = sin(enemy.frame * 0.2) * 80.0;
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
    // Random spread shot
    let angle = get_random() * 0.5 - 0.25;
    spawn_bullet("enemy", enemy.x - 15.0, enemy.y, -280.0 + angle * 50.0, angle * 200.0, 5);
}
