//! Game simulation - the main game loop.
//!
//! This module contains the deterministic game simulation that can be run
//! identically on all clients for lockstep multiplayer.

use astranyx_physics::{MovementConfig, PlayerController};
use glam::Vec3;
use serde::{Deserialize, Serialize};

use crate::input::PlayerInput;
use crate::level::Level;
use crate::player::{EntityId, Player};

/// Game simulation configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimulationConfig {
    /// Simulation tick rate (ticks per second).
    pub tick_rate: u32,

    /// Movement physics configuration.
    pub movement: MovementConfig,

    /// Mouse sensitivity.
    pub mouse_sensitivity: f32,
}

impl Default for SimulationConfig {
    fn default() -> Self {
        Self {
            tick_rate: 60,
            movement: MovementConfig::default(),
            mouse_sensitivity: 2.0,
        }
    }
}

impl SimulationConfig {
    /// Get the time step per tick in seconds.
    pub fn delta_time(&self) -> f32 {
        1.0 / self.tick_rate as f32
    }
}

/// The main game simulation.
///
/// This contains all game state and advances it deterministically based on
/// player inputs. For lockstep multiplayer, all clients run the same
/// simulation with the same inputs.
#[derive(Debug)]
pub struct Simulation {
    /// Current frame/tick number.
    pub frame: u64,

    /// Simulation configuration.
    pub config: SimulationConfig,

    /// Current level.
    pub level: Level,

    /// All players in the game.
    pub players: Vec<Player>,

    /// Movement physics controller.
    movement_controller: PlayerController,

    /// Next entity ID to assign.
    next_entity_id: EntityId,
}

impl Simulation {
    /// Create a new simulation with the given configuration and level.
    pub fn new(config: SimulationConfig, level: Level) -> Self {
        let movement_controller = PlayerController::new(config.movement.clone());

        Self {
            frame: 0,
            config,
            level,
            players: Vec::new(),
            movement_controller,
            next_entity_id: 1,
        }
    }

    /// Create a simulation with default configuration and test arena.
    pub fn test() -> Self {
        Self::new(SimulationConfig::default(), Level::test_arena())
    }

    /// Add a player to the simulation.
    ///
    /// Returns the player's ID.
    pub fn add_player(&mut self, name: &str) -> EntityId {
        let id = self.next_entity_id;
        self.next_entity_id += 1;

        // Find a spawn point
        let spawn_index = self.players.len() % self.level.player_spawn_count().max(1);
        let spawn = self.level.get_player_spawn(spawn_index);

        let position = spawn.map(|s| s.position).unwrap_or(Vec3::ZERO);
        let facing = spawn.map(|s| s.facing).unwrap_or(0.0);

        let mut player = Player::new(id, name.to_string(), position);
        player.movement.view_angles.y = facing;

        self.players.push(player);
        id
    }

    /// Remove a player from the simulation.
    pub fn remove_player(&mut self, player_id: EntityId) {
        self.players.retain(|p| p.id != player_id);
    }

    /// Get a player by ID.
    pub fn get_player(&self, player_id: EntityId) -> Option<&Player> {
        self.players.iter().find(|p| p.id == player_id)
    }

    /// Get a mutable reference to a player by ID.
    pub fn get_player_mut(&mut self, player_id: EntityId) -> Option<&mut Player> {
        self.players.iter_mut().find(|p| p.id == player_id)
    }

    /// Advance the simulation by one tick.
    ///
    /// # Arguments
    ///
    /// * `inputs` - Player inputs indexed by player position in the `players` array
    pub fn tick(&mut self, inputs: &[PlayerInput]) {
        let delta_time = self.config.delta_time();

        // Update each player
        for (i, player) in self.players.iter_mut().enumerate() {
            // Get input for this player (default if not provided)
            let input = inputs.get(i).cloned().unwrap_or_default();

            // Convert input to physics command
            let command = input.to_command(self.config.mouse_sensitivity);

            // Update movement physics
            self.movement_controller.update(
                &mut player.movement,
                &command,
                &self.level.collision,
                delta_time,
            );

            // Update timers
            player.update_timers();

            // Handle firing
            if input.actions.fire && player.can_fire() {
                player.fire_cooldown = Player::FIRE_RATE;
                // TODO: Spawn projectile
            }
        }

        // Check triggers for all players
        for player in &self.players {
            if player.is_alive() {
                let triggered = self.level.check_triggers(player.position());
                for trigger_id in triggered {
                    log::debug!("Player {} triggered: {}", player.id, trigger_id);
                    // TODO: Handle trigger events
                }
            }
        }

        // TODO: Update projectiles
        // TODO: Update enemies
        // TODO: Handle collisions

        self.frame += 1;
    }

    /// Get the delta time for this simulation.
    pub fn delta_time(&self) -> f32 {
        self.config.delta_time()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simulation_creation() {
        let sim = Simulation::test();
        assert_eq!(sim.frame, 0);
        assert!(sim.players.is_empty());
    }

    #[test]
    fn test_add_player() {
        let mut sim = Simulation::test();

        let id = sim.add_player("Player1");
        assert!(id > 0);
        assert_eq!(sim.players.len(), 1);

        let player = sim.get_player(id).unwrap();
        assert_eq!(player.name, "Player1");
        assert!(player.is_alive());
    }

    #[test]
    fn test_tick_advances_frame() {
        let mut sim = Simulation::test();
        sim.add_player("Test");

        sim.tick(&[PlayerInput::default()]);
        assert_eq!(sim.frame, 1);

        sim.tick(&[PlayerInput::default()]);
        assert_eq!(sim.frame, 2);
    }

    #[test]
    fn test_movement_input() {
        let mut sim = Simulation::test();
        let id = sim.add_player("Test");

        let start_pos = sim.get_player(id).unwrap().position();

        // Move forward for several frames
        let mut input = PlayerInput::default();
        input.movement.forward = true;

        for _ in 0..60 {
            sim.tick(&[input.clone()]);
        }

        let end_pos = sim.get_player(id).unwrap().position();
        let distance = (end_pos - start_pos).length();

        assert!(distance > 1.0, "Player should have moved, distance={}", distance);
    }

    #[test]
    fn test_determinism() {
        // Run simulation twice with same inputs - should get same results
        let inputs: Vec<_> = (0..100)
            .map(|i| {
                let mut input = PlayerInput::default();
                input.movement.forward = i % 2 == 0;
                input.movement.right = i % 3 == 0;
                input.actions.jump = i % 10 == 0;
                input
            })
            .collect();

        // First run
        let mut sim1 = Simulation::test();
        sim1.add_player("Test");
        for input in &inputs {
            sim1.tick(&[input.clone()]);
        }

        // Second run
        let mut sim2 = Simulation::test();
        sim2.add_player("Test");
        for input in &inputs {
            sim2.tick(&[input.clone()]);
        }

        // Compare results
        let pos1 = sim1.get_player(1).unwrap().position();
        let pos2 = sim2.get_player(1).unwrap().position();

        assert!(
            (pos1 - pos2).length() < 0.0001,
            "Simulations should be deterministic: {:?} vs {:?}",
            pos1,
            pos2
        );
    }
}
