// CLASSIC Boss (Type 0) - Basic boss with 4 rotating attack patterns
// First boss encountered, teaches players boss mechanics

const STATS = #{
    health: 500,
    points: 5000,
    hitbox_radius: 40.0,
    phases: 2,
    name: "CLASSIC",
};

fn get_stats() { STATS }

// Get current phase based on health percentage
fn get_phase(boss) {
    let pct = boss.health / STATS.health;
    if pct > 0.5 { 0 } else { 1 }
}

// Movement - vertical sine wave
fn update(boss, dt) {
    let wave = sin(boss.frame * 0.03) * 100.0;
    #{
        vx: 0.0,
        vy: wave * dt * 60.0
    }
}

// Should shoot based on timer (handled by engine)
fn should_shoot(boss) {
    boss.frame % 90 == 0
}

// Main shoot function - cycles through 4 patterns
fn shoot(boss) {
    let pattern = (boss.frame / 100) % 4;

    if pattern == 0 {
        shoot_aimed(boss);
    } else if pattern == 1 {
        shoot_spread(boss);
    } else if pattern == 2 {
        shoot_circle(boss);
    } else {
        shoot_rapid(boss);
    }
}

// Pattern 0: Single aimed shot at player
fn shoot_aimed(boss) {
    let player = get_nearest_player(boss.x, boss.y);
    if player != () {
        let dir = normalize(player.x - boss.x, player.y - boss.y);
        spawn_bullet("big", boss.x - 40.0, boss.y, dir.x * 250.0, dir.y * 250.0, 15);
    }
}

// Pattern 1: 5-bullet spread
fn shoot_spread(boss) {
    for i in range(-2, 3) {
        let angle = i * 0.26; // ~15 degrees
        let vx = cos(angle) * -300.0;
        let vy = sin(angle) * 300.0;
        spawn_bullet("enemy", boss.x - 40.0, boss.y, vx, vy, 8);
    }
}

// Pattern 2: 12-bullet circle
fn shoot_circle(boss) {
    for i in range(0, 12) {
        let angle = i * 0.5236; // 30 degrees
        let vx = cos(angle) * 150.0;
        let vy = sin(angle) * 150.0;
        spawn_bullet("enemy", boss.x, boss.y, vx, vy, 5);
    }
}

// Pattern 3: Triple rapid aimed shots
fn shoot_rapid(boss) {
    let player = get_nearest_player(boss.x, boss.y);
    if player != () {
        for i in range(-1, 2) {
            let spread = i * 0.1;
            let dir = normalize(player.x - boss.x, player.y - boss.y + spread * 100.0);
            spawn_bullet("enemy", boss.x - 40.0, boss.y, dir.x * 400.0, dir.y * 400.0, 5);
        }
    }
}

// Phase transition effects
fn on_phase_change(boss, new_phase) {
    spawn_particles(boss.x, boss.y, 30);
    screen_shake(0.4);
}

// Death effects
fn on_death(boss) {
    spawn_particles(boss.x, boss.y, 50);
    screen_shake(0.8);
}
