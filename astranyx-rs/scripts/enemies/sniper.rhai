// Sniper enemy - stationary, accurate fast shots
// Stays in place and fires precisely aimed projectiles

const STATS = #{
    health: 50,
    speed: 20.0,
    points: 200,
    hitbox_radius: 16.0,
    fire_rate: 75,
    shoot_threshold: 30.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Move into position then stop
    let bounds = get_world_bounds();
    let target_x = bounds.max_x - 150.0;

    if enemy.x > target_x {
        #{
            vx: -STATS.speed * 2.0,
            vy: 0.0
        }
    } else {
        // Stationary with slight hover
        #{
            vx: 0.0,
            vy: sin(enemy.frame * 0.1) * 10.0
        }
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
        // Fast, accurate shot
        spawn_bullet("sniper", enemy.x - 20.0, enemy.y, dir.x * 600.0, dir.y * 600.0, 20);
    }
}
