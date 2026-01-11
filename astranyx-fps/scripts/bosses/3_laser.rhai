// LASER Boss (Type 3) - Charges and fires devastating beam attacks
// Fourth boss, requires learning charge patterns and dodging beams

const STATS = #{
    health: 1500,
    points: 15000,
    hitbox_radius: 42.0,
    phases: 3,
    name: "LASER",
    charge_time: 120,    // Frames to charge beam
    beam_duration: 60,   // Frames beam is active
};

fn get_stats() { STATS }

fn get_phase(boss) {
    let pct = boss.health / STATS.health;
    if pct > 0.66 { 0 }
    else if pct > 0.33 { 1 }
    else { 2 }
}

// Movement - stays on right side, moves vertically to aim
fn update(boss, dt) {
    let phase = get_phase(boss);

    // During charge, track player slowly
    if is_charging(boss) {
        let player = get_nearest_player(boss.x, boss.y);
        if player != () {
            let diff = player.y - boss.y;
            let track_speed = 30.0 + phase * 10.0;
            #{
                vx: 0.0,
                vy: if abs(diff) > 5.0 { (if diff > 0.0 { track_speed } else { -track_speed }) } else { 0.0 }
            }
        } else {
            #{ vx: 0.0, vy: 0.0 }
        }
    } else {
        // Normal movement - sine wave
        let wave = sin(boss.frame * 0.025) * 70.0;
        #{
            vx: 0.0,
            vy: wave * dt * 60.0
        }
    }
}

// Check if currently charging
fn is_charging(boss) {
    // Use frame timing for charge state
    let cycle = boss.frame % 300;
    cycle >= 180 && cycle < 300
}

// Check if beam is firing
fn is_firing_beam(boss) {
    let cycle = boss.frame % 300;
    cycle >= 240 && cycle < 300
}

fn should_shoot(boss) {
    !is_charging(boss) && boss.frame % 80 == 0
}

fn shoot(boss) {
    let phase = get_phase(boss);

    if is_firing_beam(boss) {
        fire_beam(boss, phase);
    } else if !is_charging(boss) {
        // Normal attacks between beams
        shoot_normal(boss, phase);
    }
}

fn shoot_normal(boss, phase) {
    // Aimed shots
    let player = get_nearest_player(boss.x, boss.y);
    if player != () {
        let dir = normalize(player.x - boss.x, player.y - boss.y);
        spawn_bullet("enemy", boss.x - 35.0, boss.y, dir.x * 300.0, dir.y * 300.0, 8);

        if phase >= 1 {
            // Extra side shots
            spawn_bullet("enemy", boss.x - 30.0, boss.y - 20.0, -280.0, -80.0, 6);
            spawn_bullet("enemy", boss.x - 30.0, boss.y + 20.0, -280.0, 80.0, 6);
        }
    }
}

fn fire_beam(boss, phase) {
    // Beam is a series of fast, piercing projectiles
    let beam_width = 20.0 + phase * 10.0;

    for i in range(0, 3) {
        let offset = (i - 1) * beam_width / 2.0;
        spawn_bullet("laser", boss.x - 50.0, boss.y + offset, -1200.0, 0.0, 25);
    }

    // Visual effect
    screen_shake(0.2);
}

// Get charge percentage for visual feedback
fn get_charge_percent(boss) {
    if !is_charging(boss) { return 0.0; }
    let cycle = boss.frame % 300;
    let charge_progress = cycle - 180;
    min(1.0, charge_progress / 60.0)
}

// Warning indicator before beam
fn should_show_warning(boss) {
    is_charging(boss) && !is_firing_beam(boss)
}

fn on_phase_change(boss, new_phase) {
    spawn_particles(boss.x, boss.y, 40);
    screen_shake(0.6);
}

fn on_death(boss) {
    spawn_particles(boss.x, boss.y, 70);
    screen_shake(1.2);

    // Death explosion beam
    for i in range(0, 8) {
        let angle = i * 0.785398;
        spawn_bullet("laser", boss.x, boss.y, cos(angle) * 400.0, sin(angle) * 400.0, 15);
    }
}
