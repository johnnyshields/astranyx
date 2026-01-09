//! Core game simulation.
//!
//! This is the deterministic heart of the game. All game logic runs here.
//! Must produce identical results on all clients for lockstep to work.

use bincode::{Decode, Encode};
use glam::Vec2;
use serde::{Deserialize, Serialize};

use crate::entities::{
    Enemy, EnemyType, EntityIdGenerator, Player, PowerUp, Projectile, ProjectileType,
};
use crate::input::PlayerInput;
use crate::physics::{circles_collide, WorldBounds};
use crate::random::SeededRandom;

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
}

/// The main simulation engine.
pub struct Simulation {
    pub config: SimulationConfig,
    pub state: GameState,
}

impl Simulation {
    pub fn new(config: SimulationConfig, seed: u32, player_count: usize) -> Self {
        Self {
            config,
            state: GameState::new(seed, player_count),
        }
    }

    /// Advance the simulation by one frame with the given player inputs.
    /// Inputs are indexed by player index.
    pub fn tick(&mut self, inputs: &[PlayerInput]) {
        self.state.frame += 1;

        // Update scroll
        self.state.scroll_offset += 60.0 / self.config.tick_rate as f32;

        // Process player inputs
        self.update_players(inputs);

        // Update entities
        self.update_projectiles();
        self.update_enemies();
        self.update_power_ups();

        // Collision detection
        self.check_collisions();

        // Spawn enemies (wave system would go here)
        self.spawn_enemies();

        // Cleanup dead entities
        self.cleanup();
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

        for enemy in &mut self.state.enemies {
            enemy.state_timer += 1;

            // Simple AI based on type
            match enemy.enemy_type {
                EnemyType::Basic => {
                    enemy.velocity = Vec2::new(-100.0, 0.0);
                }
                EnemyType::Fast => {
                    enemy.velocity = Vec2::new(-200.0, (enemy.state_timer as f32 * 0.1).sin() * 50.0);
                }
                EnemyType::Heavy => {
                    enemy.velocity = Vec2::new(-50.0, 0.0);
                }
                EnemyType::Boss => {
                    // Boss AI would be more complex
                    enemy.velocity = Vec2::new(0.0, (enemy.state_timer as f32 * 0.05).sin() * 100.0);
                }
            }

            enemy.position += enemy.velocity * dt;

            if enemy.fire_cooldown > 0 {
                enemy.fire_cooldown -= 1;
            }
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
                        self.state.score += match enemy.enemy_type {
                            EnemyType::Basic => 100,
                            EnemyType::Fast => 150,
                            EnemyType::Heavy => 500,
                            EnemyType::Boss => 10000,
                        };
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
        // Simple spawning every 60 frames (2 seconds)
        if self.state.frame % 60 == 0 && self.state.enemies.len() < 20 {
            let id = self.state.entity_ids.next();
            let y = self.state.rng.next_range(100.0, self.config.world_bounds.height() - 100.0);
            let enemy_type = if self.state.rng.next() < 0.7 {
                EnemyType::Basic
            } else if self.state.rng.next() < 0.8 {
                EnemyType::Fast
            } else {
                EnemyType::Heavy
            };

            self.state.enemies.push(Enemy::new(
                id,
                Vec2::new(self.config.world_bounds.width() + 50.0, y),
                enemy_type,
            ));
        }
    }

    fn cleanup(&mut self) {
        // Remove dead projectiles
        self.state.projectiles.retain(|p| {
            p.lifetime > 0 && !self.config.world_bounds.is_outside(p.position, 50.0)
        });

        // Remove dead enemies
        self.state.enemies.retain(|e| {
            e.is_alive() && !self.config.world_bounds.is_outside(e.position, 100.0)
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
