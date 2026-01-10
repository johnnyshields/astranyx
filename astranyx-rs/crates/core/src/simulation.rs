//! Core game simulation.
//!
//! This is the deterministic heart of the game. All game logic runs here.
//! Must produce identical results on all clients for lockstep to work.
//!
//! The simulation is split into separate domains:
//! - `shmup` - 2D side-scrolling shoot-em-up logic
//! - `fps` - First-person shooter logic
//! - Common systems (collision, spawning, etc.) work across both

pub mod fps;
pub mod shmup;

use bincode::{Decode, Encode};
use glam::Vec2;
use serde::{Deserialize, Serialize};

/// Helper macro to include a script file from the scripts directory.
macro_rules! script {
    ($path:literal) => {
        include_str!(concat!("../../../scripts/", $path))
    };
}

use crate::entities::{Enemy, EntityIdGenerator, Player, PowerUp, Projectile};
use crate::input::PlayerInput;
use crate::level::{GameMode, LevelState};
use crate::path::PathSet;
use crate::physics::WorldBounds;
use crate::random::SeededRandom;
use crate::scripting::ScriptEngine;

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
    /// Paths for on-rails movement (loaded from segments).
    pub paths: PathSet,
}

impl Simulation {
    /// Fixed delta time for determinism (1/30 sec at 30Hz).
    pub const DT: f32 = 1.0 / 30.0;

    pub fn new(config: SimulationConfig, seed: u32, player_count: usize) -> Self {
        Self {
            config,
            state: GameState::new(seed, player_count),
            scripts: ScriptEngine::new(),
            paths: PathSet::new(),
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
        let _ = self.scripts.load_segment_script_from_str("1_approach", script!("worlds/01_station/segments/1_approach.rhai"));
        let _ = self.scripts.load_segment_script_from_str("2_corridor", script!("worlds/01_station/segments/2_corridor.rhai"));
        let _ = self.scripts.load_segment_script_from_str("3_hangar", script!("worlds/01_station/segments/3_hangar.rhai"));
        let _ = self.scripts.load_segment_script_from_str("4_base", script!("worlds/01_station/segments/4_base.rhai"));
        let _ = self.scripts.load_segment_script_from_str("5_boss", script!("worlds/01_station/segments/5_boss.rhai"));
    }

    /// Initialize the level state from scripts.
    pub fn init_level_from_scripts(&mut self) {
        let world_id = self.scripts.get_start_world()
            .or_else(|| self.scripts.get_default_world().map(|s| s.to_string()));

        let Some(world_id) = world_id else {
            return;
        };

        let Some(segment_id) = self.scripts.get_world_start_segment(&world_id) else {
            return;
        };

        let segment_id = segment_id.to_string();

        self.state.level.world_id = world_id;
        self.state.level.segment_id = segment_id;

        // Set up the initial segment properly
        self.on_segment_enter();
    }

    /// Initialize the level state with a specific world.
    pub fn init_level(&mut self, world_id: &str) {
        let segment_id = self.scripts.get_world_start_segment(world_id)
            .unwrap_or_default()
            .to_string();

        self.state.level.world_id = world_id.to_string();
        self.state.level.segment_id = segment_id;

        if !self.state.level.segment_id.is_empty() {
            self.on_segment_enter();
        }
    }

    /// Advance the simulation by one frame with the given player inputs.
    pub fn tick(&mut self, inputs: &[PlayerInput]) {
        self.state.frame += 1;

        // Update level state (transitions, segment frame)
        self.update_level();

        // Update scroll (use segment's scroll config if available)
        self.update_scroll();

        // Process player inputs based on game mode
        let mode = self.state.level.mode.clone();
        match &mode {
            GameMode::SideScroll { .. } | GameMode::OnRails { .. } | GameMode::FreeFlight => {
                shmup::update_players(self, inputs);
            }
            GameMode::FirstPerson | GameMode::Turret { .. } => {
                fps::update_players(self, inputs);
            }
        }

        // Update entities based on game mode
        match &mode {
            GameMode::SideScroll { .. } | GameMode::OnRails { .. } | GameMode::FreeFlight => {
                shmup::update_projectiles(self);
                shmup::update_enemies(self);
                shmup::update_power_ups(self);
                shmup::check_collisions(self);
                shmup::spawn_enemies(self);
            }
            GameMode::FirstPerson | GameMode::Turret { .. } => {
                fps::update_projectiles(self);
                fps::update_enemies(self);
                fps::check_collisions(self);
                // FPS may have different spawning logic
            }
        }

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
        if self.state.level.transition.is_some() {
            if self.state.level.update_transition() {
                // Transition completed - set up new segment
                self.on_segment_enter();
            }
            return;
        }

        self.state.level.segment_frame += 1;
    }

    /// Called when entering a new segment.
    fn on_segment_enter(&mut self) {
        let segment_id = &self.state.level.segment_id;

        // Clear all entities from the previous segment
        self.state.enemies.clear();
        self.state.projectiles.clear();
        self.state.power_ups.clear();

        // Load segment config and apply
        if let Some(config) = self.scripts.get_segment_config(segment_id) {
            self.state.level.bounds = config.bounds.clone();
            self.state.level.mode = config.mode.clone();

            // Reset player positions based on segment config
            let player_start = config.player_start.unwrap_or_else(|| {
                // Default start positions based on game mode
                match &config.mode {
                    GameMode::SideScroll { .. } => glam::Vec3::new(200.0, 540.0, 0.0),
                    GameMode::OnRails { .. } => glam::Vec3::new(0.0, 100.0, 50.0),
                    GameMode::FreeFlight => glam::Vec3::new(0.0, 100.0, 0.0),
                    GameMode::Turret { .. } => glam::Vec3::new(0.0, 50.0, 0.0),
                    GameMode::FirstPerson => glam::Vec3::new(0.0, 5.0, 0.0),
                }
            });

            // Reset each player to the start position
            for (i, player) in self.state.players.iter_mut().enumerate() {
                let offset = (i as f32) * 50.0; // Space out multiple players
                player.position_3d = player_start + glam::Vec3::new(offset, 0.0, 0.0);
                player.position = Vec2::new(player.position_3d.x, player.position_3d.z);
                player.velocity_3d = glam::Vec3::ZERO;
                player.velocity = Vec2::ZERO;
                // Face into the room (toward -Z) in FPS mode
                player.look_yaw = if config.mode.is_first_person() {
                    std::f32::consts::PI // Face -Z direction
                } else {
                    0.0
                };
                player.look_pitch = 0.0;
            }
        }

        // Reset scroll offset
        self.state.level.scroll_offset = glam::Vec3::ZERO;
        self.state.scroll_offset = 0.0;

        // Call segment on_enter callback
        self.scripts.call_segment_on_enter(segment_id, &self.state.level);
    }

    /// Update scroll based on segment config.
    fn update_scroll(&mut self) {
        if let Some(config) = self.scripts.get_segment_config(&self.state.level.segment_id) {
            if let Some(scroll) = &config.scroll {
                let dt = 1.0 / self.config.tick_rate as f32;
                self.state.level.scroll_offset += scroll.direction * scroll.speed * dt;
                self.state.scroll_offset = self.state.level.scroll_offset.x;
            }
        } else {
            self.state.scroll_offset += 60.0 / self.config.tick_rate as f32;
        }
    }

    /// Check route triggers and initiate transitions.
    fn check_route_triggers(&mut self) {
        if self.state.level.transition.is_some() {
            return;
        }

        let current_segment = &self.state.level.segment_id;
        if current_segment.is_empty() {
            return;
        }

        let routes = self.scripts.get_routes_from(current_segment);

        for route in routes {
            if route.evaluate(&self.state.level) {
                self.scripts.call_segment_on_exit(current_segment, &self.state.level);

                self.state.level.start_transition(
                    &route.to,
                    route.transition.transition_type,
                    route.transition.duration,
                );
                break;
            }
        }
    }

    fn cleanup(&mut self) {
        self.state.projectiles.retain(|p| {
            p.lifetime > 0 && p.position.x > self.config.world_bounds.min.x - 100.0
                && p.position.x < self.config.world_bounds.max.x + 100.0
        });

        self.state.enemies.retain(|e| {
            e.is_alive() && e.position.x > self.config.world_bounds.min.x - 100.0
        });

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

    /// Debug: Skip to the next segment immediately.
    /// Returns the new segment ID if successful.
    pub fn debug_skip_to_next_segment(&mut self) -> Option<String> {
        // Don't skip if already transitioning
        if self.state.level.transition.is_some() {
            return None;
        }

        let current_segment = &self.state.level.segment_id;
        if current_segment.is_empty() {
            return None;
        }

        // Find the first route from this segment (lowest priority first, which is usually time-based)
        let routes = self.scripts.get_routes_from(current_segment);
        let route = routes.into_iter()
            .filter(|r| r.to != "victory" && r.to != "secret_area") // Skip end states
            .min_by_key(|r| r.priority)?; // Take lowest priority (normal progression)

        self.scripts.call_segment_on_exit(current_segment, &self.state.level);

        self.state.level.start_transition(
            &route.to,
            route.transition.transition_type,
            5, // Fast transition for debug (5 frames instead of normal duration)
        );

        Some(route.to.clone())
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

    #[test]
    fn segment_transition_with_scripts() {
        let config = SimulationConfig::default();
        let mut sim = Simulation::new(config, 12345, 1);
        sim.load_embedded_scripts();
        sim.init_level_from_scripts();

        // Verify we start on segment 1 (approach)
        assert_eq!(sim.state.level.segment_id, "1_approach");
        assert!(matches!(sim.state.level.mode, GameMode::SideScroll { .. }));

        // Run the simulation past the first segment's duration (1800 frames = 60 seconds)
        let inputs = vec![PlayerInput::from_bits(PlayerInput::RIGHT)];
        for _ in 0..1900 {
            sim.tick(&inputs);
        }

        // Should have transitioned to segment 2 (corridor)
        // The transition takes 45 frames, so we need to be past 1800 + 45
        assert_eq!(sim.state.level.segment_id, "2_corridor");
        assert!(matches!(sim.state.level.mode, GameMode::OnRails { .. }));
    }

    #[test]
    fn game_mode_detection() {
        use crate::level::GameMode;

        // Test 2D mode detection
        let side_scroll = GameMode::SideScroll { angle: 0.0 };
        assert!(side_scroll.is_2d());
        assert!(!side_scroll.is_first_person());
        assert!(!side_scroll.is_on_rails());

        // Test on-rails mode detection
        let on_rails = GameMode::OnRails { path_id: "test".to_string() };
        assert!(!on_rails.is_2d());
        assert!(on_rails.is_on_rails());
        assert!(!on_rails.is_first_person());

        // Test turret mode detection
        let turret = GameMode::Turret { path_id: "test".to_string() };
        assert!(!turret.is_2d());
        assert!(turret.is_on_rails());
        assert!(turret.is_first_person());

        // Test first-person mode detection
        let fps = GameMode::FirstPerson;
        assert!(!fps.is_2d());
        assert!(!fps.is_on_rails());
        assert!(fps.is_first_person());
        assert!(fps.is_3d_free());

        // Test free-flight mode detection
        let free_flight = GameMode::FreeFlight;
        assert!(!free_flight.is_2d());
        assert!(!free_flight.is_on_rails());
        assert!(free_flight.is_3d_free());
    }

    #[test]
    fn player_3d_sync() {
        use crate::entities::Player;
        use glam::{Vec2, Vec3};

        let id = crate::entities::EntityId(1);

        // Test 2D to 3D sync
        let mut player = Player::new(id, Vec2::new(100.0, 200.0));
        player.sync_2d_to_3d();
        assert_eq!(player.position_3d.x, 100.0);
        assert_eq!(player.position_3d.z, 200.0);

        // Test 3D to 2D sync
        player.position_3d = Vec3::new(300.0, 50.0, 400.0);
        player.sync_3d_to_2d();
        assert_eq!(player.position.x, 300.0);
        assert_eq!(player.position.y, 400.0);
    }
}
