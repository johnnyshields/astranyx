// Shooter enemy - aims directly at player
// Moderate health, accurate shots

const STATS = #{
    health: 40,
    speed: 50.0,
    points: 100,
    hitbox_radius: 18.0,
    fire_rate: 60,
    shoot_threshold: 25.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Straight movement with slight vertical drift
    let drift = sin(enemy.frame * 0.05) * 15.0;
    #{
        vx: -STATS.speed,
        vy: drift
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
        // Accurate aimed shot
        spawn_bullet("aimed", enemy.x - 20.0, enemy.y, dir.x * 350.0, dir.y * 350.0, 8);
    }
}
