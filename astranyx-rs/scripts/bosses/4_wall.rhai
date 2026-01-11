// WALL Boss (Type 4) - Segmented boss with 7 destructible parts
// Fifth boss, requires destroying segments while avoiding attacks

const STATS = #{
    health: 2000,
    points: 20000,
    hitbox_radius: 55.0,
    phases: 4,
    name: "WALL",
    segment_count: 7,
    segment_health: 100,
    segment_spacing: 35.0,
};

fn get_stats() { STATS }

fn get_phase(boss) {
    let pct = boss.health / STATS.health;
    if pct > 0.75 { 0 }
    else if pct > 0.5 { 1 }
    else if pct > 0.25 { 2 }
    else { 3 }
}

// Initialize segment data (called once on spawn)
fn init_segments() {
    let segments = [];
    for i in range(-3, 4) {
        segments += #{
            y_offset: i * STATS.segment_spacing,
            health: STATS.segment_health,
            alive: true,
        };
    }
    segments
}

// Movement - slow advance then hold position
fn update(boss, dt) {
    // Slight vertical oscillation
    let wave = sin(boss.frame * 0.015) * 20.0;
    #{
        vx: 0.0,
        vy: wave * dt * 60.0
    }
}

fn should_shoot(boss) {
    boss.frame % 60 == 0
}

fn shoot(boss) {
    let phase = get_phase(boss);

    // Each living segment can fire
    shoot_from_segments(boss, phase);

    // Additional attacks based on phase
    if phase >= 2 {
        shoot_crossfire(boss);
    }
    if phase >= 3 {
        shoot_sweep(boss);
    }
}

// Each segment fires independently
fn shoot_from_segments(boss, phase) {
    for i in range(0, STATS.segment_count) {
        let y_offset = (i - 3) * STATS.segment_spacing;
        let segment_y = boss.y + y_offset;

        // Segments fire at different intervals based on position
        if (boss.frame + i * 15) % (90 - phase * 10) == 0 {
            // Aimed shot
            let player = get_nearest_player(boss.x, segment_y);
            if player != () {
                let dir = normalize(player.x - boss.x, player.y - segment_y);
                spawn_bullet("enemy", boss.x - 40.0, segment_y, dir.x * 250.0, dir.y * 250.0, 7);
            }
        }
    }
}

// Cross pattern between segments
fn shoot_crossfire(boss) {
    if boss.frame % 120 == 0 {
        // Top segments fire down, bottom fire up
        for i in range(0, 3) {
            let top_y = boss.y - (i + 1) * STATS.segment_spacing;
            let bot_y = boss.y + (i + 1) * STATS.segment_spacing;
            spawn_bullet("enemy", boss.x - 30.0, top_y, -200.0, 100.0, 5);
            spawn_bullet("enemy", boss.x - 30.0, bot_y, -200.0, -100.0, 5);
        }
    }
}

// Sweeping pattern across all segments
fn shoot_sweep(boss) {
    if boss.frame % 180 == 0 {
        for i in range(0, STATS.segment_count) {
            let y_offset = (i - 3) * STATS.segment_spacing;
            // Staggered timing creates sweep effect
            let delay = i * 5;
            spawn_bullet("enemy", boss.x - 35.0, boss.y + y_offset, -350.0, 0.0, 6);
        }
        screen_shake(0.2);
    }
}

// Damage a specific segment
fn damage_segment(boss, segment_index, damage) {
    // Return remaining health (0 if destroyed)
    // Actual segment tracking handled by engine
    max(0, STATS.segment_health - damage)
}

// Get segment Y positions for collision detection
fn get_segment_positions(boss) {
    let positions = [];
    for i in range(0, STATS.segment_count) {
        positions += boss.y + (i - 3) * STATS.segment_spacing;
    }
    positions
}

fn on_segment_destroyed(boss, segment_index) {
    let y_offset = (segment_index - 3) * STATS.segment_spacing;
    spawn_particles(boss.x, boss.y + y_offset, 20);
    screen_shake(0.3);

    // Destroyed segment explodes
    for i in range(0, 6) {
        let angle = i * 1.047;
        spawn_bullet("enemy", boss.x, boss.y + y_offset, cos(angle) * 150.0, sin(angle) * 150.0, 5);
    }
}

fn on_phase_change(boss, new_phase) {
    spawn_particles(boss.x, boss.y, 45);
    screen_shake(0.7);
}

fn on_death(boss) {
    // Chain explosion through all segments
    for i in range(0, STATS.segment_count) {
        let y_offset = (i - 3) * STATS.segment_spacing;
        spawn_particles(boss.x, boss.y + y_offset, 25);
    }
    screen_shake(1.5);
}
