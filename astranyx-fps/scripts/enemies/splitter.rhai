// Splitter enemy - splits into 2 smaller enemies on death
// Erratic movement, spawns grunts when killed

const STATS = #{
    health: 80,
    speed: 60.0,
    points: 200,
    hitbox_radius: 22.0,
    fire_rate: 80,
    shoot_threshold: 30.0,
};

fn get_stats() { STATS }

fn update(enemy, dt) {
    // Erratic zigzag movement
    let zigzag = 0.0;
    let phase = (enemy.frame / 20) % 4;
    if phase == 0 { zigzag = 80.0; }
    else if phase == 1 { zigzag = -80.0; }
    else if phase == 2 { zigzag = 60.0; }
    else { zigzag = -60.0; }

    #{
        vx: -STATS.speed,
        vy: zigzag
    }
}

fn should_shoot(enemy) {
    let bounds = get_world_bounds();
    enemy.x < bounds.max_x - STATS.shoot_threshold
}

fn shoot(enemy) {
    // Spread shot
    spawn_bullet("enemy", enemy.x - 15.0, enemy.y, -250.0, -50.0, 5);
    spawn_bullet("enemy", enemy.x - 15.0, enemy.y, -250.0, 50.0, 5);
}

// Called when splitter dies - spawn 2 grunts
fn on_death(enemy) {
    spawn_enemy("grunt", enemy.x, enemy.y - 30.0);
    spawn_enemy("grunt", enemy.x, enemy.y + 30.0);
    spawn_particles(enemy.x, enemy.y, 15);
}
