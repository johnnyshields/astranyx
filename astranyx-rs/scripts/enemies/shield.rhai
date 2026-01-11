// Shield enemy - has protective shield that must be broken first
// Shield absorbs damage before health is affected

const STATS = #{
    health: 100,
    speed: 45.0,
    points: 250,
    hitbox_radius: 24.0,
    fire_rate: 70,
    shoot_threshold: 40.0,
    shield_health: 50,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Protective sine movement
    let wave = sin(enemy.frame * 0.06) * 50.0;
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
        // Double shot
        spawn_bullet("enemy", enemy.x - 20.0, enemy.y - 10.0, dir.x * 280.0, dir.y * 280.0, 6);
        spawn_bullet("enemy", enemy.x - 20.0, enemy.y + 10.0, dir.x * 280.0, dir.y * 280.0, 6);
    }
}
