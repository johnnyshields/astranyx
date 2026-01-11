// TWIN Boss (Type 1) - Two-part boss with synchronized attacks
// Second boss, two bodies that move independently

const STATS = #{
    health: 750,
    points: 7500,
    hitbox_radius: 35.0,
    phases: 2,
    name: "TWIN",
};

fn get_stats() { STATS }

fn get_phase(boss) {
    let pct = boss.health / STATS.health;
    if pct > 0.5 { 0 } else { 1 }
}

// Movement - main body moves in figure-8 pattern
fn update(boss, dt) {
    let t = boss.frame * 0.04;
    let vx = cos(t) * 30.0;
    let vy = sin(t * 2.0) * 80.0;
    #{
        vx: vx,
        vy: vy,
        // Twin offset stored in custom data
        twin_y: sin(boss.frame * 0.05) * 120.0
    }
}

fn should_shoot(boss) {
    boss.frame % 75 == 0
}

// Both bodies shoot
fn shoot(boss) {
    let phase = get_phase(boss);
    let twin_y = sin(boss.frame * 0.05) * 120.0;

    // Main body attacks
    shoot_main(boss);

    // Twin body attacks (offset position)
    shoot_twin(boss, twin_y);
}

fn shoot_main(boss) {
    let player = get_nearest_player(boss.x, boss.y);
    if player != () {
        let dir = normalize(player.x - boss.x, player.y - boss.y);
        spawn_bullet("enemy", boss.x - 30.0, boss.y, dir.x * 280.0, dir.y * 280.0, 8);
    }
}

fn shoot_twin(boss, twin_offset) {
    let twin_y = boss.y + twin_offset;
    let player = get_nearest_player(boss.x, twin_y);
    if player != () {
        let dir = normalize(player.x - boss.x, player.y - twin_y);
        spawn_bullet("enemy", boss.x - 30.0, twin_y, dir.x * 280.0, dir.y * 280.0, 8);
    }

    // Cross-fire pattern
    spawn_bullet("enemy", boss.x - 20.0, twin_y, -250.0, 100.0, 5);
    spawn_bullet("enemy", boss.x - 20.0, twin_y, -250.0, -100.0, 5);
}

// Special synchronized attack every 200 frames
fn special_attack(boss) {
    if boss.frame % 200 == 0 {
        let twin_y = sin(boss.frame * 0.05) * 120.0;

        // Both bodies fire circle patterns
        for i in range(0, 8) {
            let angle = i * 0.785398; // 45 degrees
            let vx = cos(angle) * 180.0;
            let vy = sin(angle) * 180.0;
            spawn_bullet("enemy", boss.x, boss.y, vx, vy, 6);
            spawn_bullet("enemy", boss.x, boss.y + twin_y, vx, vy, 6);
        }
    }
}

fn on_phase_change(boss, new_phase) {
    spawn_particles(boss.x, boss.y, 25);
    spawn_particles(boss.x, boss.y + sin(boss.frame * 0.05) * 120.0, 25);
    screen_shake(0.5);
}

fn on_death(boss) {
    spawn_particles(boss.x, boss.y, 40);
    spawn_particles(boss.x, boss.y + sin(boss.frame * 0.05) * 120.0, 40);
    screen_shake(0.9);
}
