//! Core game simulation.
//!
//! This is the deterministic heart of the game. All game logic runs here.
//! Must produce identical results on all clients for lockstep to work.

use bincode::{Decode, Encode};
use glam::Vec2;
use serde::{Deserialize, Serialize};

/// Helper macro to include a script file from the scripts directory.
macro_rules! script {
    ($path:literal) => {
        include_str!(concat!("../../../scripts/", $path))
    };
}

use crate::entities::{
    Enemy, EnemyType, EntityId, EntityIdGenerator, Player, PowerUp, Projectile, ProjectileType,
};
use crate::input::PlayerInput;
use crate::level::LevelState;
use crate::physics::{circles_collide, WorldBounds};
use crate::random::SeededRandom;
use crate::scripting::{ScriptEngine, ScriptEnemy};

/// Configuration for the simulation.
#[derive(Debug, Clone)]
pub struct SimulationConfig {
    pub world_bounds: WorldBounds,
    pub tick_rate: u32,
    pub max_players: usize,
}

impl Default for SimulationConfig {
    fn default() -> Self {
        Self {
            world_bounds: WorldBounds::default(),
            tick_rate: 30,
            max_players: 4,
        }
    }
}

/// The complete game state - everything needed to simulate one frame.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct GameState {
    pub frame: u32,
    pub players: Vec<Player>,
    pub projectiles: Vec<Projectile>,
    pub enemies: Vec<Enemy>,
    pub power_ups: Vec<PowerUp>,
    pub scroll_offset: f32,
    pub score: u32,
    pub rng: SeededRandom,
    pub entity_ids: EntityIdGenerator,
    /// Level state (world, segment, transitions).
    pub level: LevelState,
}

impl GameState {
    pub fn new(seed: u32, player_count: usize) -> Self {
        let mut state = Self {
            frame: 0,
            players: Vec::with_capacity(4),
            projectiles: Vec::with_capacity(256),
            enemies: Vec::with_capacity(64),
            power_ups: Vec::with_capacity(16),
            scroll_offset: 0.0,
            score: 0,
            rng: SeededRandom::new(seed),
            entity_ids: EntityIdGenerator::new(),
            level: LevelState::default(),
        };

        // Spawn players
        for i in 0..player_count {
            let id = state.entity_ids.next();
            let y_offset = (i as f32 - (player_count as f32 - 1.0) / 2.0) * 100.0;
            let position = Vec2::new(200.0, 540.0 + y_offset);
            state.players.push(Player::new(id, position));
        }

        state
    }

    /// Create game state with a specific world and segment.
    pub fn new_with_level(seed: u32, player_count: usize, world_id: &str, segment_id: &str) -> Self {
        let mut state = Self::new(seed, player_count);
        state.level = LevelState::new(world_id, segment_id);
        state
    }
}

/// The main simulation engine.
pub struct Simulation {
    pub config: SimulationConfig,
    pub state: GameState,
    pub scripts: ScriptEngine,
}

impl Simulation {
    pub fn new(config: SimulationConfig, seed: u32, player_count: usize) -> Self {
        Self {
            config,
            state: GameState::new(seed, player_count),
            scripts: ScriptEngine::new(),
        }
    }

    /// Load scripts from a directory.
    pub fn load_scripts(&mut self, scripts_path: &std::path::Path) -> Result<(), String> {
        self.scripts.load_scripts_from_dir(scripts_path)
            .map_err(|e| e.to_string())
    }

    /// Load scripts from embedded strings (for WASM builds).
    pub fn load_embedded_scripts(&mut self) {
        // Game config (must be loaded first)
        let _ = self.scripts.load_config_script_from_str(script!("config.rhai"));

        // Enemy scripts
        let _ = self.scripts.load_enemy_script_from_str("grunt", script!("enemies/grunt.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("shooter", script!("enemies/shooter.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("swerver", script!("enemies/swerver.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("tank", script!("enemies/tank.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("speeder", script!("enemies/speeder.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("bomber", script!("enemies/bomber.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("sniper", script!("enemies/sniper.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("carrier", script!("enemies/carrier.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("mine", script!("enemies/mine.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("spiral", script!("enemies/spiral.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("shield", script!("enemies/shield.rhai"));
        let _ = self.scripts.load_enemy_script_from_str("splitter", script!("enemies/splitter.rhai"));

        // Wave system
        let _ = self.scripts.load_wave_script_from_str(script!("waves/wave_system.rhai"));

        // Weapons and powerups
        let _ = self.scripts.load_weapons_script_from_str(script!("weapons/weapons.rhai"));
        let _ = self.scripts.load_powerups_script_from_str(script!("powerups/powerups.rhai"));

        // World 01: Space Station
        let _ = self.scripts.load_world_script_from_str("station", script!("worlds/01_station/world.rhai"));
        let _ = self.scripts.load_route_script_from_str(script!("worlds/01_station/routes.rhai"));
        let _ = self.scripts.load_segment_script_from_str("station_approach", script!("worlds/01_station/segments/station_approach.rhai"));
        let _ = self.scripts.load_segment_script_from_str("station_interior", script!("worlds/01_station/segments/station_interior.rhai"));
        let _ = self.scripts.load_segment_script_from_str("station_hangar", script!("worlds/01_station/segments/station_hangar.rhai"));
    }

    /// Initialize the level state from scripts.
    /// Uses the start_world from config.rhai and the world's starting segment.
    pub fn init_level_from_scripts(&mut self) {
        // Get starting world from config, fallback to first loaded world
        let world_id = self.scripts.get_start_world()
            .or_else(|| self.scripts.get_default_world().map(|s| s.to_string()));

        let Some(world_id) = world_id else {
            return;
        };

        // Get starting segment for this world
        let Some(segment_id) = self.scripts.get_world_start_segment(&world_id) else {
            return;
        };

        let segment_id = segment_id.to_string();

        self.state.level.world_id = world_id;
        self.state.level.segment_id = segment_id.clone();

        // Apply segment config (bounds, mode)
        if let Some(config) = self.scripts.get_segment_config(&segment_id) {
            self.state.level.bounds = config.bounds;
            self.state.level.mode = config.mode;
        }

        // Call on_enter for the initial segment
        self.scripts.call_segment_on_enter(&segment_id, &self.state.level);
    }

    /// Initialize the level state with a specific world.
    pub fn init_level(&mut self, world_id: &str) {
        // Get starting segment for this world
        let segment_id = self.scripts.get_world_start_segment(world_id)
            .unwrap_or_default()
            .to_string();

        self.state.level.world_id = world_id.to_string();
        self.state.level.segment_id = segment_id.clone();

        // Apply segment config (bounds, mode)
        if let Some(config) = self.scripts.get_segment_config(&segment_id) {
            self.state.level.bounds = config.bounds;
            self.state.level.mode = config.mode;
        }

        // Call on_enter for the initial segment
        if !segment_id.is_empty() {
            self.scripts.call_segment_on_enter(&segment_id, &self.state.level);
        }
    }

    /// Advance the simulation by one frame with the given player inputs.
    /// Inputs are indexed by player index.
    pub fn tick(&mut self, inputs: &[PlayerInput]) {
        self.state.frame += 1;

        // Update level state (transitions, segment frame)
        self.update_level();

        // Update scroll (use segment's scroll config if available)
        self.update_scroll();

        // Process player inputs
        self.update_players(inputs);

        // Update entities
        self.update_projectiles();
        self.update_enemies();
        self.update_power_ups();

        // Collision detection
        self.check_collisions();

        // Spawn enemies (segment-aware spawning)
        self.spawn_enemies();

        // Call segment tick callback
        self.scripts.call_segment_on_tick(
            &self.state.level.segment_id,
            &self.state.level,
            self.state.level.segment_frame,
        );

        // Check route triggers for transitions
        self.check_route_triggers();

        // Cleanup dead entities
        self.cleanup();
    }

    /// Update level state (transitions, segment frame).
    fn update_level(&mut self) {
        // Handle active transition
        if self.state.level.transition.is_some() {
            if self.state.level.update_transition() {
                // Transition completed - call on_enter for new segment
                self.scripts.call_segment_on_enter(
                    &self.state.level.segment_id,
                    &self.state.level,
                );

                // Apply new segment's bounds and mode
                if let Some(config) = self.scripts.get_segment_config(&self.state.level.segment_id) {
                    self.state.level.bounds = config.bounds;
                    self.state.level.mode = config.mode;
                }
            }
            return; // Skip normal updates during transition
        }

        // Increment segment frame
        self.state.level.segment_frame += 1;
    }

    /// Update scroll based on segment config.
    fn update_scroll(&mut self) {
        // Get scroll config from current segment
        if let Some(config) = self.scripts.get_segment_config(&self.state.level.segment_id) {
            if let Some(scroll) = &config.scroll {
                let dt = 1.0 / self.config.tick_rate as f32;
                self.state.level.scroll_offset += scroll.direction * scroll.speed * dt;
                self.state.scroll_offset = self.state.level.scroll_offset.x;
            }
        } else {
            // Fallback: default scroll
            self.state.scroll_offset += 60.0 / self.config.tick_rate as f32;
        }
    }

    /// Check route triggers and initiate transitions.
    fn check_route_triggers(&mut self) {
        // Skip if already transitioning
        if self.state.level.transition.is_some() {
            return;
        }

        let current_segment = &self.state.level.segment_id;
        if current_segment.is_empty() {
            return;
        }

        // Get routes from the current segment
        let routes = self.scripts.get_routes_from(current_segment);

        // Evaluate triggers in priority order (routes should be sorted)
        for route in routes {
            if route.evaluate(&self.state.level) {
                // Call on_exit for current segment
                self.scripts.call_segment_on_exit(current_segment, &self.state.level);

                // Start transition
                self.state.level.start_transition(
                    &route.to,
                    route.transition.transition_type,
                    route.transition.duration,
                );
                break;
            }
        }
    }

    fn update_players(&mut self, inputs: &[PlayerInput]) {
        let dt = 1.0 / self.config.tick_rate as f32;

        for (i, player) in self.state.players.iter_mut().enumerate() {
            if !player.is_alive() {
                continue;
            }

            let input = inputs.get(i).copied().unwrap_or_default();

            // Movement
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

            player.position += player.velocity * dt;
            player.position = self
                .config
                .world_bounds
                .clamp_with_radius(player.position, Player::HITBOX_RADIUS);

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

                let bullet_id = self.state.entity_ids.next();
                self.state.projectiles.push(Projectile::new(
                    bullet_id,
                    player.position + Vec2::new(20.0, 0.0),
                    Vec2::new(800.0, 0.0),
                    10,
                    player.id,
                    ProjectileType::PlayerBullet,
                ));
            }
        }
    }

    fn update_projectiles(&mut self) {
        let dt = 1.0 / self.config.tick_rate as f32;

        for proj in &mut self.state.projectiles {
            proj.position += proj.velocity * dt;
            if proj.lifetime > 0 {
                proj.lifetime -= 1;
            }
        }
    }

    fn update_enemies(&mut self) {
        let dt = 1.0 / self.config.tick_rate as f32;
        let bounds = &self.config.world_bounds;

        // Collect enemy shooting info first to avoid borrow issues
        let mut shots_to_fire: Vec<(Vec2, Vec2)> = Vec::new();

        for enemy in &mut self.state.enemies {
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
            if let Some((vx, vy)) = self.scripts.update_enemy(script_name, &script_enemy, dt) {
                enemy.velocity = Vec2::new(vx, vy);
            } else {
                // Minimal fallback - just move left
                enemy.velocity = Vec2::new(-80.0, 0.0);
            }

            enemy.position += enemy.velocity * dt;

            // Clamp Y to bounds
            enemy.position.y = enemy.position.y.clamp(bounds.min.y + 50.0, bounds.max.y - 50.0);

            // Enemy shooting (when on screen and cooldown ready)
            if enemy.fire_cooldown > 0 {
                enemy.fire_cooldown -= 1;
            } else if enemy.position.x < bounds.max.x - 100.0 {
                // Get fire rate from script stats
                let shoot_rate = self.scripts.get_enemy_stats(script_name)
                    .map(|s| s.fire_rate)
                    .unwrap_or(90);

                enemy.fire_cooldown = shoot_rate;

                // Queue a shot toward the left
                shots_to_fire.push((
                    enemy.position + Vec2::new(-20.0, 0.0),
                    Vec2::new(-300.0, 0.0),
                ));
            }
        }

        // Create projectiles from queued shots
        for (pos, vel) in shots_to_fire {
            let id = self.state.entity_ids.next();
            self.state.projectiles.push(Projectile::new(
                id,
                pos,
                vel,
                5,
                EntityId(0), // Enemy owner
                ProjectileType::EnemyBullet,
            ));
        }
    }

    fn update_power_ups(&mut self) {
        let dt = 1.0 / self.config.tick_rate as f32;

        for power_up in &mut self.state.power_ups {
            power_up.position += power_up.velocity * dt;
            if power_up.lifetime > 0 {
                power_up.lifetime -= 1;
            }
        }
    }

    fn check_collisions(&mut self) {
        // Player bullets vs enemies
        for proj in &mut self.state.projectiles {
            if !matches!(proj.projectile_type, ProjectileType::PlayerBullet | ProjectileType::PlayerMissile) {
                continue;
            }

            for enemy in &mut self.state.enemies {
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
                    proj.lifetime = 0; // Mark for removal

                    if !enemy.is_alive() {
                        // Get points from script stats
                        let points = self.scripts.get_enemy_stats(enemy.enemy_type.script_name())
                            .map(|s| s.points)
                            .unwrap_or(100);
                        self.state.score += points;
                    }
                    break;
                }
            }
        }

        // Enemy bullets vs players
        for proj in &mut self.state.projectiles {
            if !matches!(proj.projectile_type, ProjectileType::EnemyBullet | ProjectileType::EnemyLaser) {
                continue;
            }

            for player in &mut self.state.players {
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
                    player.invincibility_frames = 90; // 3 seconds
                    proj.lifetime = 0;
                    break;
                }
            }
        }

        // Enemies vs players (collision damage)
        for enemy in &self.state.enemies {
            if !enemy.is_alive() {
                continue;
            }

            for player in &mut self.state.players {
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
        for power_up in &mut self.state.power_ups {
            for player in &mut self.state.players {
                if !player.is_alive() {
                    continue;
                }

                if circles_collide(
                    player.position,
                    Player::HITBOX_RADIUS,
                    power_up.position,
                    PowerUp::HITBOX_RADIUS,
                ) {
                    // Apply power-up effect
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

    fn spawn_enemies(&mut self) {
        // Spawn enemies every 30 frames (1 second at 30Hz) with some randomness
        // More frequent spawning for a shoot-em-up feel
        let spawn_interval = 30 + (self.state.rng.next() * 30.0) as u32;

        if self.state.frame % spawn_interval == 0 && self.state.enemies.len() < 15 {
            // Spawn 1-3 enemies at a time
            let count = 1 + (self.state.rng.next() * 2.0) as usize;

            // Calculate "wave" based on time for progressive unlocks
            let wave = (self.state.frame / 300) as u32; // New wave every 10 seconds

            for _ in 0..count {
                let id = self.state.entity_ids.next();
                // Spawn at right edge of screen, random Y within play area
                let y = self.state.rng.next_range(100.0, self.config.world_bounds.height() - 100.0);

                // Pick enemy type based on wave progression
                let roll = self.state.rng.next();
                let enemy_type = self.pick_enemy_type(wave, roll);

                // Spawn at right edge (within bounds so they don't get culled)
                self.state.enemies.push(Enemy::new(
                    id,
                    Vec2::new(self.config.world_bounds.max.x - 10.0, y),
                    enemy_type,
                ));
            }
        }
    }

    /// Pick an enemy type based on wave and random roll.
    fn pick_enemy_type(&self, wave: u32, roll: f32) -> EnemyType {
        // Use wave system script to get available enemies
        let available = self.scripts.get_available_enemies(wave);

        // Pick from available types
        let idx = (roll * available.len() as f32) as usize;
        let name = &available[idx.min(available.len() - 1)];
        EnemyType::from_script_name(name)
    }

    fn cleanup(&mut self) {
        // Remove dead projectiles or ones that left the play area (left side)
        self.state.projectiles.retain(|p| {
            p.lifetime > 0 && p.position.x > self.config.world_bounds.min.x - 100.0
                && p.position.x < self.config.world_bounds.max.x + 100.0
        });

        // Remove dead enemies or ones that left the left side of the screen
        self.state.enemies.retain(|e| {
            e.is_alive() && e.position.x > self.config.world_bounds.min.x - 100.0
        });

        // Remove expired power-ups
        self.state.power_ups.retain(|p| {
            p.lifetime > 0 && !self.config.world_bounds.is_outside(p.position, 50.0)
        });
    }

    /// Get the current frame number.
    pub fn frame(&self) -> u32 {
        self.state.frame
    }

    /// Serialize the current state for rollback/sync.
    pub fn serialize_state(&self) -> Vec<u8> {
        bincode::encode_to_vec(&self.state, bincode::config::standard())
            .expect("serialization should not fail")
    }

    /// Deserialize and restore state.
    pub fn deserialize_state(&mut self, data: &[u8]) -> Result<(), bincode::error::DecodeError> {
        let (state, _): (GameState, _) =
            bincode::decode_from_slice(data, bincode::config::standard())?;
        self.state = state;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simulation_determinism() {
        let config = SimulationConfig::default();
        let mut sim1 = Simulation::new(config.clone(), 12345, 2);
        let mut sim2 = Simulation::new(config, 12345, 2);

        let inputs = vec![
            PlayerInput::from_bits(PlayerInput::RIGHT | PlayerInput::FIRE),
            PlayerInput::from_bits(PlayerInput::UP),
        ];

        for _ in 0..1000 {
            sim1.tick(&inputs);
            sim2.tick(&inputs);
        }

        // States should be identical
        assert_eq!(sim1.state.frame, sim2.state.frame);
        assert_eq!(sim1.state.score, sim2.state.score);
        assert_eq!(sim1.state.players.len(), sim2.state.players.len());

        for (p1, p2) in sim1.state.players.iter().zip(sim2.state.players.iter()) {
            assert_eq!(p1.position, p2.position);
            assert_eq!(p1.health, p2.health);
        }
    }

    #[test]
    fn state_serialization_roundtrip() {
        let config = SimulationConfig::default();
        let mut sim = Simulation::new(config.clone(), 42, 1);

        let inputs = vec![PlayerInput::from_bits(PlayerInput::FIRE)];
        for _ in 0..100 {
            sim.tick(&inputs);
        }

        let serialized = sim.serialize_state();
        let mut sim2 = Simulation::new(config, 0, 1);
        sim2.deserialize_state(&serialized).unwrap();

        assert_eq!(sim.state.frame, sim2.state.frame);
        assert_eq!(sim.state.score, sim2.state.score);
    }
}
