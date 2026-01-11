//! FPS (first-person shooter) simulation domain.
//!
//! MGS-inspired stealth-action gameplay with:
//! - Vision cone system for enemy detection
//! - Alert state machine (unaware -> curious -> alert -> combat -> search)
//! - Sound propagation for footsteps, gunfire, environmental
//! - Stealth player mechanics (crouch, cover, prone)
//!
//! This module is isolated from the shmup code for clean separation.

pub mod alert;
pub mod collision;
pub mod movement;
pub mod sound;
pub mod stealth;
pub mod vision;

use glam::{Vec2, Vec3};

use crate::entities::{EntityId, Player, Projectile, ProjectileType};
use crate::input::PlayerInput;
use crate::level::GameMode;

use super::Simulation;

pub use alert::{AlertLevel, AlertState};
pub use sound::{SoundEvent, SoundType};
pub use stealth::StealthState;
pub use vision::VisionCone;

/// FPS-specific enemy state extension.
/// Stored separately to avoid bloating the base Enemy struct.
#[derive(Debug, Clone, Default)]
pub struct FpsEnemyState {
    /// Current alert state
    pub alert: AlertState,
    /// Vision cone configuration
    pub vision: VisionCone,
    /// Last known player position (for searching)
    pub last_known_player_pos: Option<Vec3>,
    /// Patrol waypoints (if any)
    pub patrol_points: Vec<Vec3>,
    /// Current patrol index
    pub patrol_index: usize,
    /// Facing direction (yaw in radians)
    pub facing_yaw: f32,
}

/// Sound events queued this frame for propagation.
#[derive(Debug, Clone, Default)]
pub struct FpsSoundQueue {
    pub events: Vec<SoundEvent>,
}

impl FpsSoundQueue {
    pub fn clear(&mut self) {
        self.events.clear();
    }

    pub fn push(&mut self, event: SoundEvent) {
        self.events.push(event);
    }
}

/// FPS game state extension - stored in Simulation.
#[derive(Debug, Clone, Default)]
pub struct FpsState {
    /// Per-enemy FPS state (indexed same as sim.state.enemies)
    pub enemy_states: Vec<FpsEnemyState>,
    /// Sound events this frame
    pub sound_queue: FpsSoundQueue,
    /// Global alert modifier (0.0 = calm, 1.0 = high alert)
    pub alert_modifier: f32,
    /// Frames since last alert (for cooldown)
    pub frames_since_alert: u32,
}

impl FpsState {
    pub fn new() -> Self {
        Self::default()
    }

    /// Ensure enemy_states matches the enemy count.
    pub fn sync_enemy_count(&mut self, enemy_count: usize) {
        while self.enemy_states.len() < enemy_count {
            self.enemy_states.push(FpsEnemyState::default());
        }
        self.enemy_states.truncate(enemy_count);
    }
}

/// Update all players in FPS mode.
pub fn update_players(sim: &mut Simulation, inputs: &[PlayerInput]) {
    let mode = sim.state.level.mode.clone();
    let bounds_3d = sim.state.level.bounds;
    let segment_frame = sim.state.level.segment_frame;

    // Get geometry for collision detection
    let geometry: Vec<crate::level::segment::GeometryDef> = sim.scripts
        .get_segment_config(&sim.state.level.segment_id)
        .map(|c| c.geometry)
        .unwrap_or_default();

    // Collect projectiles to spawn
    let mut projectiles_to_spawn: Vec<(Vec3, Vec3, i32, EntityId)> = Vec::new();
    // Collect sound events
    let mut sound_events: Vec<SoundEvent> = Vec::new();

    for (i, player) in sim.state.players.iter_mut().enumerate() {
        if !player.is_alive() {
            continue;
        }

        let input = inputs.get(i).copied().unwrap_or_default();

        // Mode-specific movement
        match &mode {
            GameMode::FirstPerson => {
                let sounds = movement::update_player_fps_with_collision(player, &input, &bounds_3d, &geometry);
                sound_events.extend(sounds);
            }
            GameMode::Turret { path_id } => {
                movement::update_player_turret(player, &input, path_id, &sim.paths, segment_frame);
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

        // Firing - 3D projectile in look direction
        if input.fire() && player.fire_cooldown == 0 {
            player.fire_cooldown = Player::FIRE_RATE;

            let forward = player.forward_3d();
            let spawn_pos = player.position_3d + forward * 2.0 + Vec3::new(0.0, 1.5, 0.0);

            projectiles_to_spawn.push((spawn_pos, forward * 800.0, 10, player.id));

            // Gunfire is LOUD - alerts enemies in large radius
            sound_events.push(SoundEvent {
                position: player.position_3d,
                sound_type: SoundType::Gunfire,
                radius: 500.0,
                source_entity: Some(player.id),
            });
        }
    }

    // Spawn projectiles (converted to 2D for now, until we have 3D projectiles)
    for (pos, vel, damage, owner) in projectiles_to_spawn {
        let bullet_id = sim.state.entity_ids.next();
        sim.state.projectiles.push(Projectile::new(
            bullet_id,
            Vec2::new(pos.x, pos.z),
            Vec2::new(vel.x, vel.z),
            damage,
            owner,
            ProjectileType::PlayerBullet,
        ));
    }

    // Queue sound events for processing
    // (Would be processed in update_enemies for alert system)
    let _ = sound_events; // TODO: integrate with FpsState
}

/// Update projectiles in FPS mode.
pub fn update_projectiles(sim: &mut Simulation) {
    for proj in &mut sim.state.projectiles {
        proj.position += proj.velocity * Simulation::DT;
        if proj.lifetime > 0 {
            proj.lifetime -= 1;
        }
    }
}

/// Update enemies in FPS mode with stealth AI.
pub fn update_enemies(sim: &mut Simulation) {
    let player_positions: Vec<(EntityId, Vec3, StealthState)> = sim
        .state
        .players
        .iter()
        .filter(|p| p.is_alive())
        .map(|p| (p.id, p.position_3d, StealthState::from_player(p)))
        .collect();

    for (idx, enemy) in sim.state.enemies.iter_mut().enumerate() {
        enemy.state_timer += 1;

        // Simple FPS enemy behavior for now
        // TODO: integrate with FpsEnemyState for full alert system
        if !player_positions.is_empty() {
            let (_, player_pos, _stealth) = &player_positions[0];
            let to_player = Vec2::new(player_pos.x, player_pos.z) - enemy.position;

            // Move toward player slowly
            if to_player.length() > 100.0 {
                enemy.velocity = to_player.normalize() * 30.0;
            } else {
                enemy.velocity = Vec2::ZERO;
            }
        }

        enemy.position += enemy.velocity * Simulation::DT;

        // Enemy shooting toward player
        if enemy.fire_cooldown > 0 {
            enemy.fire_cooldown -= 1;
        } else if !player_positions.is_empty() {
            enemy.fire_cooldown = 60;

            let (_, player_pos, _) = &player_positions[0];
            let to_player =
                (Vec2::new(player_pos.x, player_pos.z) - enemy.position).normalize_or_zero();

            let id = sim.state.entity_ids.next();
            sim.state.projectiles.push(Projectile::new(
                id,
                enemy.position,
                to_player * 200.0,
                5,
                EntityId(0),
                ProjectileType::EnemyBullet,
            ));
        }

        let _ = idx; // TODO: use for FpsEnemyState lookup
    }
}

/// Check collisions in FPS mode.
pub fn check_collisions(sim: &mut Simulation) {
    use crate::physics::circles_collide;

    // Player bullets vs enemies (using 2D projection)
    for proj in &mut sim.state.projectiles {
        if !matches!(
            proj.projectile_type,
            ProjectileType::PlayerBullet | ProjectileType::PlayerMissile
        ) {
            continue;
        }

        for enemy in &mut sim.state.enemies {
            if !enemy.is_alive() {
                continue;
            }

            // FPS uses larger hitboxes since aiming is harder
            let hit_radius = enemy.hitbox_radius() * 1.5;

            if circles_collide(
                proj.position,
                proj.hitbox_radius(),
                enemy.position,
                hit_radius,
            ) {
                enemy.health -= proj.damage;
                proj.lifetime = 0;

                if !enemy.is_alive() {
                    let points = sim
                        .scripts
                        .get_enemy_stats(enemy.enemy_type.script_name())
                        .map(|s| s.points)
                        .unwrap_or(100);
                    sim.state.score += points;
                    sim.state.level.enemies_killed += 1;
                }
                break;
            }
        }
    }

    // Enemy bullets vs players (using 3D positions projected to 2D)
    for proj in &mut sim.state.projectiles {
        if !matches!(
            proj.projectile_type,
            ProjectileType::EnemyBullet | ProjectileType::EnemyLaser
        ) {
            continue;
        }

        for player in &mut sim.state.players {
            if !player.is_alive() || player.is_invincible() {
                continue;
            }

            let player_2d = Vec2::new(player.position_3d.x, player.position_3d.z);

            if circles_collide(
                proj.position,
                proj.hitbox_radius(),
                player_2d,
                Player::HITBOX_RADIUS * 2.0,
            ) {
                player.health -= proj.damage;
                player.invincibility_frames = 60;
                proj.lifetime = 0;
                sim.state.level.damage_taken += 1;
                break;
            }
        }
    }
}

/// Spawn enemies in FPS/Turret modes.
pub fn spawn_enemies(sim: &mut Simulation) {
    use crate::entities::{Enemy, EnemyType};

    // Spawn interval: 45-90 frames (1.5-3 seconds)
    let spawn_interval = 45 + (sim.state.rng.next() * 45.0) as u32;

    // Max 10 enemies in FPS mode (smaller arenas)
    if sim.state.frame % spawn_interval == 0 && sim.state.enemies.len() < 10 {
        let count = 1 + (sim.state.rng.next() * 1.5) as usize;
        let wave = (sim.state.frame / 300) as u32;
        let bounds = &sim.state.level.bounds;

        for _ in 0..count {
            let id = sim.state.entity_ids.next();

            // Spawn in front of player (in -Z direction), spread across X
            let x = sim
                .state
                .rng
                .next_range(bounds.min.x + 50.0, bounds.max.x - 50.0);
            let z = sim
                .state
                .rng
                .next_range(bounds.min.z, bounds.min.z + 100.0);
            let y = 5.0;

            let available = sim.scripts.get_available_enemies(wave);
            let idx = (sim.state.rng.next() * available.len() as f32) as usize;
            let name = &available[idx.min(available.len() - 1)];
            let enemy_type = EnemyType::from_script_name(name);

            let mut enemy = Enemy::new(id, Vec2::new(x, z), enemy_type);
            enemy.position_3d = Vec3::new(x, y, z);

            sim.state.enemies.push(enemy);
        }
    }
}
