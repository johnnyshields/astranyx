// CARRIER Boss (Type 2) - Spawns smaller enemies while fighting
// Third boss, requires dealing with adds while damaging boss

const STATS = #{
    health: 1000,
    points: 10000,
    hitbox_radius: 45.0,
    phases: 3,
    name: "CARRIER",
    spawn_cooldown: 180, // Frames between spawns
    max_spawns: 6,       // Maximum active spawned enemies
};

fn get_stats() { STATS }

fn get_phase(boss) {
    let pct = boss.health / STATS.health;
    if pct > 0.66 { 0 }
    else if pct > 0.33 { 1 }
    else { 2 }
}

// Movement - slow horizontal sweep
fn update(boss, dt) {
    let wave = sin(boss.frame * 0.02) * 60.0;
    #{
        vx: 0.0,
        vy: wave * dt * 60.0
    }
}

fn should_shoot(boss) {
    boss.frame % 100 == 0
}

fn shoot(boss) {
    let phase = get_phase(boss);

    // Base attack - spread shot
    shoot_spread(boss);

    // Phase 1+: More aggressive
    if phase >= 1 {
        shoot_homing(boss);
    }

    // Phase 2: Maximum aggression
    if phase >= 2 {
        shoot_barrage(boss);
    }
}

fn shoot_spread(boss) {
    for i in range(-2, 3) {
        let angle = i * 0.2;
        spawn_bullet("enemy", boss.x - 35.0, boss.y, cos(angle) * -220.0, sin(angle) * 220.0, 6);
    }
}

fn shoot_homing(boss) {
    let player = get_nearest_player(boss.x, boss.y);
    if player != () {
        let dir = normalize(player.x - boss.x, player.y - boss.y);
        spawn_bullet("big", boss.x - 40.0, boss.y, dir.x * 200.0, dir.y * 200.0, 12);
    }
}

fn shoot_barrage(boss) {
    // Rain of bullets from top and bottom
    spawn_bullet("enemy", boss.x - 20.0, boss.y - 30.0, -300.0, 0.0, 5);
    spawn_bullet("enemy", boss.x - 20.0, boss.y + 30.0, -300.0, 0.0, 5);
}

// Spawn enemies periodically
fn should_spawn_enemy(boss) {
    let phase = get_phase(boss);
    let cooldown = STATS.spawn_cooldown - phase * 30; // Faster spawns in later phases
    boss.frame % cooldown == 0
}

fn spawn_minion(boss) {
    let phase = get_phase(boss);

    // Spawn position offset
    let offset_y = (get_random() - 0.5) * 100.0;

    // Enemy type depends on phase
    if phase == 0 {
        spawn_enemy("grunt", boss.x - 60.0, boss.y + offset_y);
    } else if phase == 1 {
        // Mix of grunts and shooters
        if get_random() > 0.5 {
            spawn_enemy("shooter", boss.x - 60.0, boss.y + offset_y);
        } else {
            spawn_enemy("grunt", boss.x - 60.0, boss.y + offset_y);
        }
    } else {
        // Phase 2: Stronger enemies
        let rng = get_random();
        if rng > 0.7 {
            spawn_enemy("swerver", boss.x - 60.0, boss.y + offset_y);
        } else if rng > 0.4 {
            spawn_enemy("shooter", boss.x - 60.0, boss.y + offset_y);
        } else {
            spawn_enemy("speeder", boss.x - 60.0, boss.y + offset_y);
        }
    }

    spawn_particles(boss.x - 50.0, boss.y + offset_y, 8);
}

fn on_phase_change(boss, new_phase) {
    spawn_particles(boss.x, boss.y, 35);
    screen_shake(0.5);

    // Spawn a wave of enemies on phase change
    for i in range(0, 3) {
        let offset = (i - 1) * 60.0;
        spawn_enemy("grunt", boss.x - 80.0, boss.y + offset);
    }
}

fn on_death(boss) {
    spawn_particles(boss.x, boss.y, 60);
    screen_shake(1.0);
}
