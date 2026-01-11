// FINAL Boss (Type 5) - Ultimate boss combining all patterns
// Final boss with 5 phases, uses attacks from all previous bosses

const STATS = #{
    health: 3000,
    points: 30000,
    hitbox_radius: 50.0,
    phases: 5,
    name: "FINAL",
};

fn get_stats() { STATS }

fn get_phase(boss) {
    let pct = boss.health / STATS.health;
    if pct > 0.8 { 0 }
    else if pct > 0.6 { 1 }
    else if pct > 0.4 { 2 }
    else if pct > 0.2 { 3 }
    else { 4 }
}

// Movement changes based on phase
fn update(boss, dt) {
    let phase = get_phase(boss);

    if phase == 0 {
        // Phase 0: Classic sine wave
        let wave = sin(boss.frame * 0.03) * 80.0;
        #{ vx: 0.0, vy: wave * dt * 60.0 }
    } else if phase == 1 {
        // Phase 1: Twin figure-8
        let t = boss.frame * 0.04;
        #{ vx: cos(t) * 25.0, vy: sin(t * 2.0) * 70.0 }
    } else if phase == 2 {
        // Phase 2: Carrier slow sweep
        let wave = sin(boss.frame * 0.02) * 50.0;
        #{ vx: 0.0, vy: wave * dt * 60.0 }
    } else if phase == 3 {
        // Phase 3: Laser tracking
        let player = get_nearest_player(boss.x, boss.y);
        if player != () {
            let diff = player.y - boss.y;
            let track_speed = 50.0;
            #{ vx: 0.0, vy: if abs(diff) > 5.0 { (if diff > 0.0 { track_speed } else { -track_speed }) } else { 0.0 } }
        } else {
            #{ vx: 0.0, vy: 0.0 }
        }
    } else {
        // Phase 4: Aggressive chase
        let player = get_nearest_player(boss.x, boss.y);
        if player != () {
            let dir = normalize(player.x - boss.x, player.y - boss.y);
            #{ vx: dir.x * 40.0, vy: dir.y * 60.0 }
        } else {
            #{ vx: 0.0, vy: 0.0 }
        }
    }
}

fn should_shoot(boss) {
    let phase = get_phase(boss);
    let rate = 80 - phase * 10; // Gets faster each phase
    boss.frame % rate == 0
}

fn shoot(boss) {
    let phase = get_phase(boss);

    // Each phase uses different attack patterns
    if phase == 0 {
        phase0_attack(boss);
    } else if phase == 1 {
        phase1_attack(boss);
    } else if phase == 2 {
        phase2_attack(boss);
    } else if phase == 3 {
        phase3_attack(boss);
    } else {
        phase4_attack(boss);
    }

    // Desperation attacks (low health)
    if boss.health < STATS.health * 0.1 {
        desperation_attack(boss);
    }
}

// Phase 0: Classic boss patterns
fn phase0_attack(boss) {
    let pattern = (boss.frame / 100) % 4;

    if pattern == 0 {
        // Aimed shot
        let player = get_nearest_player(boss.x, boss.y);
        if player != () {
            let dir = normalize(player.x - boss.x, player.y - boss.y);
            spawn_bullet("big", boss.x - 40.0, boss.y, dir.x * 280.0, dir.y * 280.0, 18);
        }
    } else if pattern == 1 {
        // 5-bullet spread
        for i in range(-2, 3) {
            let angle = i * 0.26;
            spawn_bullet("enemy", boss.x - 40.0, boss.y, cos(angle) * -320.0, sin(angle) * 320.0, 10);
        }
    } else if pattern == 2 {
        // 16-bullet circle
        for i in range(0, 16) {
            let angle = i * 0.3927;
            spawn_bullet("enemy", boss.x, boss.y, cos(angle) * 180.0, sin(angle) * 180.0, 6);
        }
    } else {
        // Rapid triple
        let player = get_nearest_player(boss.x, boss.y);
        if player != () {
            for i in range(-1, 2) {
                let spread = i * 0.12;
                let dir = normalize(player.x - boss.x, player.y - boss.y + spread * 100.0);
                spawn_bullet("enemy", boss.x - 40.0, boss.y, dir.x * 450.0, dir.y * 450.0, 7);
            }
        }
    }
}

// Phase 1: Twin boss dual attacks
fn phase1_attack(boss) {
    let twin_y = sin(boss.frame * 0.05) * 100.0;

    // Main body
    let player = get_nearest_player(boss.x, boss.y);
    if player != () {
        let dir = normalize(player.x - boss.x, player.y - boss.y);
        spawn_bullet("enemy", boss.x - 30.0, boss.y, dir.x * 300.0, dir.y * 300.0, 9);
    }

    // Virtual twin
    let player2 = get_nearest_player(boss.x, boss.y + twin_y);
    if player2 != () {
        let dir2 = normalize(player2.x - boss.x, player2.y - (boss.y + twin_y));
        spawn_bullet("enemy", boss.x - 30.0, boss.y + twin_y, dir2.x * 300.0, dir2.y * 300.0, 9);
    }

    // Cross-fire
    spawn_bullet("enemy", boss.x - 20.0, boss.y, -270.0, 120.0, 6);
    spawn_bullet("enemy", boss.x - 20.0, boss.y + twin_y, -270.0, -120.0, 6);
}

// Phase 2: Carrier spawning + attacks
fn phase2_attack(boss) {
    // Spread shot
    for i in range(-3, 4) {
        let angle = i * 0.18;
        spawn_bullet("enemy", boss.x - 35.0, boss.y, cos(angle) * -240.0, sin(angle) * 240.0, 7);
    }

    // Spawn enemies periodically
    if boss.frame % 150 == 0 {
        let rng = get_random();
        let offset_y = (rng - 0.5) * 120.0;
        if rng > 0.5 {
            spawn_enemy("shooter", boss.x - 70.0, boss.y + offset_y);
        } else {
            spawn_enemy("grunt", boss.x - 70.0, boss.y + offset_y);
        }
        spawn_particles(boss.x - 60.0, boss.y + offset_y, 10);
    }
}

// Phase 3: Laser charging and beam
fn phase3_attack(boss) {
    let cycle = boss.frame % 200;

    if cycle >= 150 && cycle < 200 {
        // Firing beam
        for i in range(0, 4) {
            let offset = (i - 1.5) * 15.0;
            spawn_bullet("laser", boss.x - 50.0, boss.y + offset, -1400.0, 0.0, 30);
        }
        if cycle == 150 {
            screen_shake(0.3);
        }
    } else if cycle < 100 {
        // Normal attacks while not charging
        let player = get_nearest_player(boss.x, boss.y);
        if player != () {
            let dir = normalize(player.x - boss.x, player.y - boss.y);
            spawn_bullet("enemy", boss.x - 35.0, boss.y, dir.x * 350.0, dir.y * 350.0, 10);
        }
    }
    // Frames 100-150: Charging (visual indicator in engine)
}

// Phase 4: Wall-style multi-point attacks
fn phase4_attack(boss) {
    // Multiple attack points
    let offsets = [-80.0, -40.0, 0.0, 40.0, 80.0];

    for offset in offsets {
        let attack_y = boss.y + offset;

        if boss.frame % 50 == 0 {
            let player = get_nearest_player(boss.x, attack_y);
            if player != () {
                let dir = normalize(player.x - boss.x, player.y - attack_y);
                spawn_bullet("enemy", boss.x - 35.0, attack_y, dir.x * 300.0, dir.y * 300.0, 8);
            }
        }
    }

    // Sweep attack
    if boss.frame % 120 == 0 {
        for offset in offsets {
            spawn_bullet("enemy", boss.x - 40.0, boss.y + offset, -400.0, 0.0, 7);
        }
        screen_shake(0.2);
    }
}

// Desperation: Everything at once
fn desperation_attack(boss) {
    if boss.frame % 30 == 0 {
        // Circle burst
        for i in range(0, 12) {
            let angle = i * 0.5236 + boss.frame * 0.02;
            spawn_bullet("enemy", boss.x, boss.y, cos(angle) * 200.0, sin(angle) * 200.0, 8);
        }

        // Aimed
        let player = get_nearest_player(boss.x, boss.y);
        if player != () {
            let dir = normalize(player.x - boss.x, player.y - boss.y);
            spawn_bullet("big", boss.x - 45.0, boss.y, dir.x * 350.0, dir.y * 350.0, 20);
        }
    }
}

fn on_phase_change(boss, new_phase) {
    spawn_particles(boss.x, boss.y, 50);
    screen_shake(0.8);

    // Dramatic phase transition
    for i in range(0, 12) {
        let angle = i * 0.5236;
        spawn_bullet("enemy", boss.x, boss.y, cos(angle) * 150.0, sin(angle) * 150.0, 5);
    }
}

fn on_death(boss) {
    // Epic death sequence
    for wave in range(0, 5) {
        for i in range(0, 16) {
            let angle = i * 0.3927 + wave * 0.2;
            let speed = 150.0 + wave * 50.0;
            spawn_bullet("enemy", boss.x, boss.y, cos(angle) * speed, sin(angle) * speed, 3);
        }
    }

    spawn_particles(boss.x, boss.y, 100);
    screen_shake(2.0);
}
