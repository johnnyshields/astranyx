//! Shmup (shoot-em-up) simulation domain.
//!
//! Handles 2D side-scrolling, on-rails, and free-flight gameplay modes.
//! All entities use 2D positions in the XY plane.

use glam::{Vec2, Vec3};

use crate::entities::{EntityId, Player, PowerUp, Projectile, ProjectileType};
use crate::input::PlayerInput;
use crate::level::GameMode;
use crate::scripting::ScriptEnemy;

use super::Simulation;

/// Update all players in shmup mode.
pub fn update_players(sim: &mut Simulation, inputs: &[PlayerInput]) {
    let mode = sim.state.level.mode.clone();
    let segment_frame = sim.state.level.segment_frame;

    // Collect projectiles to spawn
    let mut projectiles_to_spawn: Vec<(Vec2, Vec2, i32, EntityId)> = Vec::new();

    for (i, player) in sim.state.players.iter_mut().enumerate() {
        if !player.is_alive() {
            continue;
        }

        let input = inputs.get(i).copied().unwrap_or_default();

        // Mode-specific movement
        match &mode {
            GameMode::SideScroll { .. } => {
                update_player_2d(player, &input, &sim.config.world_bounds);
            }
            GameMode::OnRails { path_id } => {
                update_player_on_rails(player, &input, path_id, &sim.paths, segment_frame);
            }
            GameMode::FreeFlight => {
                update_player_flight(player, &input, &sim.state.level.bounds);
            }
            _ => {}
        }

        // Cooldowns
        if player.fire_cooldown > 0 {
            player.fire_cooldown -= 1;
        }
        if player.invincibility_frames > 0 {
            player.invincibility_frames -= 1;
        }

        // Firing
        if input.fire() && player.fire_cooldown == 0 {
            player.fire_cooldown = Player::FIRE_RATE;
            projectiles_to_spawn.push((
                player.position + Vec2::new(20.0, 0.0),
                Vec2::new(800.0, 0.0),
                10,
                player.id,
            ));
        }
    }

    // Spawn projectiles
    for (pos, vel, damage, owner) in projectiles_to_spawn {
        let bullet_id = sim.state.entity_ids.next();
        sim.state.projectiles.push(Projectile::new(
            bullet_id,
            pos,
            vel,
            damage,
            owner,
            ProjectileType::PlayerBullet,
        ));
    }
}

/// 2D side-scroll movement.
fn update_player_2d(
    player: &mut Player,
    input: &PlayerInput,
    bounds: &crate::physics::WorldBounds,
) {
    let speed = if input.focus() {
        Player::FOCUS_SPEED
    } else {
        Player::SPEED
    };

    let move_dir = Vec2::new(input.horizontal() as f32, input.vertical() as f32);
    if move_dir != Vec2::ZERO {
        player.velocity = move_dir.normalize() * speed;
    } else {
        player.velocity = Vec2::ZERO;
    }

    player.position += player.velocity * Simulation::DT;
    player.position = bounds.clamp_with_radius(player.position, Player::HITBOX_RADIUS);
    player.sync_2d_to_3d();
}

/// On-rails movement (Starfox-style).
fn update_player_on_rails(
    player: &mut Player,
    input: &PlayerInput,
    path_id: &str,
    paths: &crate::path::PathSet,
    frame: u32,
) {
    if let Some(path) = paths.get(path_id) {
        let (path_pos, path_rot) = path.sample_at_frame(frame);

        // Dodge movement perpendicular to path
        let dodge_speed = 150.0;
        let dodge_x = input.horizontal() as f32 * dodge_speed * Simulation::DT;
        let dodge_y = input.vertical() as f32 * dodge_speed * Simulation::DT;

        let right = Vec3::new(path_rot.x, 0.0, path_rot.z).normalize_or_zero();
        let up = Vec3::Y;

        player.position_3d = path_pos + right * dodge_x + up * dodge_y;

        // Clamp dodge range
        let max_dodge = 100.0;
        let offset = player.position_3d - path_pos;
        if offset.length() > max_dodge {
            player.position_3d = path_pos + offset.normalize() * max_dodge;
        }
    }

    player.sync_3d_to_2d();
}

/// Free-flight movement (Rogue Squadron style).
fn update_player_flight(
    player: &mut Player,
    input: &PlayerInput,
    bounds: &crate::physics::WorldBounds3D,
) {
    // Mouse look
    let (dx, dy) = input.mouse_delta_radians(0.003);
    player.look_yaw += dx;
    player.look_pitch = (player.look_pitch + dy).clamp(-Player::MAX_PITCH, Player::MAX_PITCH);

    // Flight controls
    let forward = player.forward_3d();
    let right = player.right_3d();
    let up = Vec3::Y;

    let mut move_dir = Vec3::ZERO;
    if input.forward() {
        move_dir += forward;
    }
    if input.backward() {
        move_dir -= forward;
    }
    if input.left() {
        move_dir -= right;
    }
    if input.right() {
        move_dir += right;
    }
    if input.up() {
        move_dir += up;
    }
    if input.down() {
        move_dir -= up;
    }

    let speed = Player::FPS_SPEED * 2.0;
    if move_dir.length_squared() > 0.0 {
        player.velocity_3d = move_dir.normalize() * speed;
    } else {
        player.velocity_3d *= 0.95;
    }

    player.position_3d += player.velocity_3d * Simulation::DT;
    player.position_3d = player.position_3d.clamp(bounds.min, bounds.max);
    player.sync_3d_to_2d();
}

/// Update projectiles in shmup mode.
pub fn update_projectiles(sim: &mut Simulation) {
    for proj in &mut sim.state.projectiles {
        proj.position += proj.velocity * Simulation::DT;
        if proj.lifetime > 0 {
            proj.lifetime -= 1;
        }
    }
}

/// Update enemies in shmup mode.
pub fn update_enemies(sim: &mut Simulation) {
    let bounds = &sim.config.world_bounds;

    // Collect shots to fire
    let mut shots_to_fire: Vec<(Vec2, Vec2)> = Vec::new();

    for enemy in &mut sim.state.enemies {
        enemy.state_timer += 1;

        // Convert to script enemy
        let script_enemy = ScriptEnemy {
            id: enemy.id.0,
            x: enemy.position.x,
            y: enemy.position.y,
            vx: enemy.velocity.x,
            vy: enemy.velocity.y,
            health: enemy.health,
            frame: enemy.state_timer,
        };

        let script_name = enemy.enemy_type.script_name();

        // Get velocity from script
        if let Some((vx, vy)) = sim.scripts.update_enemy(script_name, &script_enemy, Simulation::DT) {
            enemy.velocity = Vec2::new(vx, vy);
        } else {
            enemy.velocity = Vec2::new(-80.0, 0.0);
        }

        enemy.position += enemy.velocity * Simulation::DT;
        enemy.position.y = enemy.position.y.clamp(bounds.min.y + 50.0, bounds.max.y - 50.0);

        // Enemy shooting
        if enemy.fire_cooldown > 0 {
            enemy.fire_cooldown -= 1;
        } else if enemy.position.x < bounds.max.x - 100.0 {
            let shoot_rate = sim.scripts.get_enemy_stats(script_name)
                .map(|s| s.fire_rate)
                .unwrap_or(90);

            enemy.fire_cooldown = shoot_rate;
            shots_to_fire.push((
                enemy.position + Vec2::new(-20.0, 0.0),
                Vec2::new(-300.0, 0.0),
            ));
        }
    }

    // Create projectiles
    for (pos, vel) in shots_to_fire {
        let id = sim.state.entity_ids.next();
        sim.state.projectiles.push(Projectile::new(
            id,
            pos,
            vel,
            5,
            EntityId(0),
            ProjectileType::EnemyBullet,
        ));
    }
}

/// Update power-ups.
pub fn update_power_ups(sim: &mut Simulation) {
    for power_up in &mut sim.state.power_ups {
        power_up.position += power_up.velocity * Simulation::DT;
        if power_up.lifetime > 0 {
            power_up.lifetime -= 1;
        }
    }
}

/// Check collisions in shmup mode.
pub fn check_collisions(sim: &mut Simulation) {
    use crate::physics::circles_collide;

    // Player bullets vs enemies
    for proj in &mut sim.state.projectiles {
        if !matches!(proj.projectile_type, ProjectileType::PlayerBullet | ProjectileType::PlayerMissile) {
            continue;
        }

        for enemy in &mut sim.state.enemies {
            if !enemy.is_alive() {
                continue;
            }

            if circles_collide(
                proj.position,
                proj.hitbox_radius(),
                enemy.position,
                enemy.hitbox_radius(),
            ) {
                enemy.health -= proj.damage;
                proj.lifetime = 0;

                if !enemy.is_alive() {
                    let points = sim.scripts.get_enemy_stats(enemy.enemy_type.script_name())
                        .map(|s| s.points)
                        .unwrap_or(100);
                    sim.state.score += points;
                }
                break;
            }
        }
    }

    // Enemy bullets vs players
    for proj in &mut sim.state.projectiles {
        if !matches!(proj.projectile_type, ProjectileType::EnemyBullet | ProjectileType::EnemyLaser) {
            continue;
        }

        for player in &mut sim.state.players {
            if !player.is_alive() || player.is_invincible() {
                continue;
            }

            if circles_collide(
                proj.position,
                proj.hitbox_radius(),
                player.position,
                Player::HITBOX_RADIUS,
            ) {
                player.health -= proj.damage;
                player.invincibility_frames = 90;
                proj.lifetime = 0;
                break;
            }
        }
    }

    // Enemies vs players (collision damage)
    for enemy in &sim.state.enemies {
        if !enemy.is_alive() {
            continue;
        }

        for player in &mut sim.state.players {
            if !player.is_alive() || player.is_invincible() {
                continue;
            }

            if circles_collide(
                player.position,
                Player::HITBOX_RADIUS,
                enemy.position,
                enemy.hitbox_radius(),
            ) {
                player.health -= 1;
                player.invincibility_frames = 90;
            }
        }
    }

    // Power-ups vs players
    for power_up in &mut sim.state.power_ups {
        for player in &mut sim.state.players {
            if !player.is_alive() {
                continue;
            }

            if circles_collide(
                player.position,
                Player::HITBOX_RADIUS,
                power_up.position,
                PowerUp::HITBOX_RADIUS,
            ) {
                match power_up.power_type {
                    crate::entities::PowerUpType::Health => {
                        player.health = (player.health + 1).min(player.max_health);
                    }
                    crate::entities::PowerUpType::Special => {
                        player.special_charge = (player.special_charge + 0.25).min(1.0);
                    }
                    _ => {}
                }
                power_up.lifetime = 0;
                break;
            }
        }
    }
}

/// Spawn enemies in shmup mode.
pub fn spawn_enemies(sim: &mut Simulation) {
    use crate::entities::EnemyType;

    let spawn_interval = 30 + (sim.state.rng.next() * 30.0) as u32;

    if sim.state.frame % spawn_interval == 0 && sim.state.enemies.len() < 15 {
        let count = 1 + (sim.state.rng.next() * 2.0) as usize;
        let wave = (sim.state.frame / 300) as u32;

        for _ in 0..count {
            let id = sim.state.entity_ids.next();
            let y = sim.state.rng.next_range(100.0, sim.config.world_bounds.height() - 100.0);
            let roll = sim.state.rng.next();

            let available = sim.scripts.get_available_enemies(wave);
            let idx = (roll * available.len() as f32) as usize;
            let name = &available[idx.min(available.len() - 1)];
            let enemy_type = EnemyType::from_script_name(name);

            sim.state.enemies.push(crate::entities::Enemy::new(
                id,
                Vec2::new(sim.config.world_bounds.max.x - 10.0, y),
                enemy_type,
            ));
        }
    }
}
