// Grunt enemy - basic cannon fodder
// Simple sine wave movement, occasional shots

const STATS = #{
    health: 20,
    speed: 80.0,
    points: 50,
    hitbox_radius: 16.0,
    fire_rate: 90,
    shoot_threshold: 20.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Sine wave movement
    let wave = sin(enemy.frame * 0.1) * 30.0;
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
    let player = get_nearest_player(enemy.x, enemy.y);
    if player != () {
        let dir = normalize(player.x - enemy.x, player.y - enemy.y);
        spawn_bullet("enemy", enemy.x - 20.0, enemy.y, dir.x * -300.0, dir.y * -300.0, 5);
    }
}
