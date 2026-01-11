// Spiral enemy - moves in spiral, fires 8-bullet spread
// Challenging enemy with circular movement

const STATS = #{
    health: 70,
    speed: 35.0,
    points: 180,
    hitbox_radius: 20.0,
    fire_rate: 60,
    shoot_threshold: 35.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Spiral movement - circle while moving left
    let angle = enemy.frame * 0.08;
    let vx = -STATS.speed + cos(angle) * 40.0;
    let vy = sin(angle) * 60.0;
    #{
        vx: vx,
        vy: vy
    }
}

fn should_shoot(enemy) {
    let bounds = get_world_bounds();
    enemy.x < bounds.max_x - STATS.shoot_threshold
}

fn shoot(enemy) {
    // 8-bullet spread in all directions
    for i in range(0, 8) {
        let angle = i * 0.785398; // 45 degrees
        let vx = cos(angle) * 200.0;
        let vy = sin(angle) * 200.0;
        spawn_bullet("enemy", enemy.x, enemy.y, vx, vy, 5);
    }
}
