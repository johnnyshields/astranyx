// Tank enemy - slow but heavily armored
// Fires frequently, takes many hits to kill

const STATS = #{
    health: 150,
    speed: 30.0,
    points: 300,
    hitbox_radius: 32.0,
    fire_rate: 45,
    shoot_threshold: 50.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Slow steady movement with gentle wave
    let wave = sin(enemy.frame * 0.03) * 20.0;
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
    // Triple shot spread
    for i in range(-1, 2) {
        let spread = i * 0.15;
        spawn_bullet("big", enemy.x - 30.0, enemy.y + i * 15.0, -200.0, spread * 100.0, 12);
    }
}
