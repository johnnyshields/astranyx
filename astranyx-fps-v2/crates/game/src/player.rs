//! Player entity and state.

use astranyx_physics::{MovementConfig, MovementState, PlayerController};
use glam::Vec3;
use serde::{Deserialize, Serialize};

/// Unique identifier for entities.
pub type EntityId = u32;

/// A player in the game.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Player {
    /// Unique player ID.
    pub id: EntityId,

    /// Player name/handle.
    pub name: String,

    /// Movement physics state.
    pub movement: MovementState,

    /// Current health (0 = dead).
    pub health: i32,

    /// Maximum health.
    pub max_health: i32,

    /// Current armor.
    pub armor: i32,

    /// Currently equipped weapon index.
    pub current_weapon: usize,

    /// Weapon fire cooldown (frames).
    pub fire_cooldown: u32,

    /// Invincibility frames after taking damage.
    pub invincibility_frames: u32,

    /// Total score.
    pub score: u32,

    /// Deaths this session.
    pub deaths: u32,

    /// Kills this session.
    pub kills: u32,
}

impl Player {
    /// Fire rate in frames (60fps = 10 shots/sec at cooldown of 6).
    pub const FIRE_RATE: u32 = 6;

    /// Invincibility duration after taking damage.
    pub const INVINCIBILITY_DURATION: u32 = 30; // 0.5s at 60fps

    /// Create a new player at the given spawn position.
    pub fn new(id: EntityId, name: String, spawn_position: Vec3) -> Self {
        Self {
            id,
            name,
            movement: MovementState::new(spawn_position),
            health: 100,
            max_health: 100,
            armor: 0,
            current_weapon: 0,
            fire_cooldown: 0,
            invincibility_frames: 0,
            score: 0,
            deaths: 0,
            kills: 0,
        }
    }

    /// Get the player's current position.
    #[inline]
    pub fn position(&self) -> Vec3 {
        self.movement.position
    }

    /// Get the player's eye position (for camera).
    pub fn eye_position(&self, config: &MovementConfig) -> Vec3 {
        self.movement.eye_position(
            config.eye_height_standing,
            config.eye_height_crouching,
        )
    }

    /// Get the direction the player is looking.
    #[inline]
    pub fn look_direction(&self) -> Vec3 {
        self.movement.look_direction()
    }

    /// Get the player's forward direction (horizontal only).
    #[inline]
    pub fn forward_direction(&self) -> Vec3 {
        self.movement.forward_direction()
    }

    /// Check if the player is alive.
    #[inline]
    pub fn is_alive(&self) -> bool {
        self.health > 0
    }

    /// Check if the player is on the ground.
    #[inline]
    pub fn on_ground(&self) -> bool {
        self.movement.flags.on_ground()
    }

    /// Check if the player is crouching.
    #[inline]
    pub fn is_crouching(&self) -> bool {
        self.movement.flags.crouching()
    }

    /// Check if the player can fire.
    #[inline]
    pub fn can_fire(&self) -> bool {
        self.is_alive() && self.fire_cooldown == 0
    }

    /// Apply damage to the player.
    ///
    /// Returns the actual damage dealt (after armor absorption).
    pub fn take_damage(&mut self, amount: i32) -> i32 {
        if !self.is_alive() || self.invincibility_frames > 0 {
            return 0;
        }

        // Armor absorbs some damage
        let armor_absorption = (self.armor.min(amount) * 2) / 3;
        self.armor = (self.armor - armor_absorption).max(0);

        let actual_damage = amount - armor_absorption;
        self.health = (self.health - actual_damage).max(0);

        if self.health > 0 {
            self.invincibility_frames = Self::INVINCIBILITY_DURATION;
        } else {
            self.die();
        }

        actual_damage
    }

    /// Heal the player.
    ///
    /// Returns the actual health restored.
    pub fn heal(&mut self, amount: i32) -> i32 {
        if !self.is_alive() {
            return 0;
        }

        let before = self.health;
        self.health = (self.health + amount).min(self.max_health);
        self.health - before
    }

    /// Add armor to the player.
    ///
    /// Returns the actual armor added.
    pub fn add_armor(&mut self, amount: i32, max_armor: i32) -> i32 {
        let before = self.armor;
        self.armor = (self.armor + amount).min(max_armor);
        self.armor - before
    }

    /// Kill the player.
    fn die(&mut self) {
        self.health = 0;
        self.deaths += 1;
        self.movement.flags.set(
            astranyx_physics::MovementFlags::DEAD,
            true,
        );
    }

    /// Respawn the player at a new position.
    pub fn respawn(&mut self, position: Vec3) {
        self.health = self.max_health;
        self.armor = 0;
        self.movement = MovementState::new(position);
        self.fire_cooldown = 0;
        self.invincibility_frames = Self::INVINCIBILITY_DURATION;
    }

    /// Update per-frame timers.
    pub fn update_timers(&mut self) {
        if self.fire_cooldown > 0 {
            self.fire_cooldown -= 1;
        }
        if self.invincibility_frames > 0 {
            self.invincibility_frames -= 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_player_creation() {
        let player = Player::new(1, "Test".to_string(), Vec3::new(0.0, 0.0, 0.0));
        assert!(player.is_alive());
        assert_eq!(player.health, 100);
    }

    #[test]
    fn test_damage() {
        let mut player = Player::new(1, "Test".to_string(), Vec3::ZERO);

        let damage = player.take_damage(30);
        assert_eq!(damage, 30);
        assert_eq!(player.health, 70);
        assert!(player.invincibility_frames > 0);
    }

    #[test]
    fn test_armor_absorption() {
        let mut player = Player::new(1, "Test".to_string(), Vec3::ZERO);
        player.armor = 50;

        let damage = player.take_damage(30);
        // Armor absorbs 2/3 of damage up to armor value
        // 30 damage, 20 absorbed by armor, 10 to health
        assert!(damage < 30);
        assert!(player.health > 70);
    }

    #[test]
    fn test_death() {
        let mut player = Player::new(1, "Test".to_string(), Vec3::ZERO);

        player.take_damage(150);
        assert!(!player.is_alive());
        assert_eq!(player.deaths, 1);
    }

    #[test]
    fn test_respawn() {
        let mut player = Player::new(1, "Test".to_string(), Vec3::ZERO);
        player.take_damage(150);

        player.respawn(Vec3::new(10.0, 0.0, 10.0));
        assert!(player.is_alive());
        assert_eq!(player.health, 100);
        assert_eq!(player.position(), Vec3::new(10.0, 0.0, 10.0));
    }
}
