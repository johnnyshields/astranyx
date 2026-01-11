// Mine enemy - stationary hazard
// Doesn't move or shoot, just blocks the path

const STATS = #{
    health: 30,
    speed: 0.0,
    points: 40,
    hitbox_radius: 20.0,
    fire_rate: 999,
    shoot_threshold: 20.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Stationary - slight pulse animation
    #{
        vx: 0.0,
        vy: 0.0
    }
}

fn should_shoot(enemy) {
    // Mines don't shoot
    false
}

fn shoot(enemy) {
    // No shooting
}

// Called when mine is destroyed - explode!
fn on_death(enemy) {
    spawn_particles(enemy.x, enemy.y, 20);
    screen_shake(0.3);
    // Spawn ring of bullets on death
    for i in range(0, 8) {
        let angle = i * 0.785398; // 45 degrees in radians
        let vx = cos(angle) * 150.0;
        let vy = sin(angle) * 150.0;
        spawn_bullet("enemy", enemy.x, enemy.y, vx, vy, 8);
    }
}
