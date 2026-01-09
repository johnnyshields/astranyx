//! Entity types and management for the simulation.
//!
//! Uses a simple array-based entity storage for deterministic iteration order.
//! No hashmaps or sets - iteration order must be identical across all clients.

use bincode::{Decode, Encode};
use glam::Vec2;
use serde::{Deserialize, Serialize};

/// Unique identifier for an entity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Encode, Decode)]
pub struct EntityId(pub u32);

/// Player ship entity.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct Player {
    pub id: EntityId,
    #[bincode(with_serde)]
    pub position: Vec2,
    #[bincode(with_serde)]
    pub velocity: Vec2,
    pub rotation: f32,
    pub health: i32,
    pub max_health: i32,
    pub invincibility_frames: u32,
    pub fire_cooldown: u32,
    pub special_charge: f32,
}

impl Player {
    pub const SPEED: f32 = 200.0;
    pub const FOCUS_SPEED: f32 = 80.0;
    pub const FIRE_RATE: u32 = 6; // Frames between shots
    pub const HITBOX_RADIUS: f32 = 4.0;

    pub fn new(id: EntityId, position: Vec2) -> Self {
        Self {
            id,
            position,
            velocity: Vec2::ZERO,
            rotation: 0.0,
            health: 3,
            max_health: 3,
            invincibility_frames: 0,
            fire_cooldown: 0,
            special_charge: 0.0,
        }
    }

    pub fn is_alive(&self) -> bool {
        self.health > 0
    }

    pub fn is_invincible(&self) -> bool {
        self.invincibility_frames > 0
    }
}

/// Projectile entity (bullets, missiles, etc).
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct Projectile {
    pub id: EntityId,
    #[bincode(with_serde)]
    pub position: Vec2,
    #[bincode(with_serde)]
    pub velocity: Vec2,
    pub damage: i32,
    pub owner: EntityId,
    pub lifetime: u32,
    pub projectile_type: ProjectileType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Encode, Decode)]
pub enum ProjectileType {
    PlayerBullet,
    PlayerMissile,
    EnemyBullet,
    EnemyLaser,
}

impl Projectile {
    pub fn new(
        id: EntityId,
        position: Vec2,
        velocity: Vec2,
        damage: i32,
        owner: EntityId,
        projectile_type: ProjectileType,
    ) -> Self {
        Self {
            id,
            position,
            velocity,
            damage,
            owner,
            lifetime: 300, // 10 seconds at 30fps
            projectile_type,
        }
    }

    pub fn hitbox_radius(&self) -> f32 {
        match self.projectile_type {
            ProjectileType::PlayerBullet => 4.0,
            ProjectileType::PlayerMissile => 8.0,
            ProjectileType::EnemyBullet => 6.0,
            ProjectileType::EnemyLaser => 3.0,
        }
    }
}

/// Enemy entity.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct Enemy {
    pub id: EntityId,
    #[bincode(with_serde)]
    pub position: Vec2,
    #[bincode(with_serde)]
    pub velocity: Vec2,
    pub health: i32,
    pub enemy_type: EnemyType,
    pub state_timer: u32,
    pub fire_cooldown: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Encode, Decode)]
pub enum EnemyType {
    Basic,
    Fast,
    Heavy,
    Boss,
}

impl Enemy {
    pub fn new(id: EntityId, position: Vec2, enemy_type: EnemyType) -> Self {
        let health = match enemy_type {
            EnemyType::Basic => 10,
            EnemyType::Fast => 5,
            EnemyType::Heavy => 50,
            EnemyType::Boss => 500,
        };

        Self {
            id,
            position,
            velocity: Vec2::ZERO,
            health,
            enemy_type,
            state_timer: 0,
            fire_cooldown: 0,
        }
    }

    pub fn hitbox_radius(&self) -> f32 {
        match self.enemy_type {
            EnemyType::Basic => 16.0,
            EnemyType::Fast => 12.0,
            EnemyType::Heavy => 32.0,
            EnemyType::Boss => 64.0,
        }
    }

    pub fn is_alive(&self) -> bool {
        self.health > 0
    }
}

/// Power-up entity.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct PowerUp {
    pub id: EntityId,
    #[bincode(with_serde)]
    pub position: Vec2,
    #[bincode(with_serde)]
    pub velocity: Vec2,
    pub power_type: PowerUpType,
    pub lifetime: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Encode, Decode)]
pub enum PowerUpType {
    Health,
    Weapon,
    Special,
    Shield,
    Speed,
}

impl PowerUp {
    pub const HITBOX_RADIUS: f32 = 12.0;

    pub fn new(id: EntityId, position: Vec2, power_type: PowerUpType) -> Self {
        Self {
            id,
            position,
            velocity: Vec2::new(-30.0, 0.0), // Drift left
            power_type,
            lifetime: 600, // 20 seconds
        }
    }
}

/// Manages entity ID generation.
#[derive(Debug, Clone, Default, Serialize, Deserialize, Encode, Decode)]
pub struct EntityIdGenerator {
    next_id: u32,
}

impl EntityIdGenerator {
    pub fn new() -> Self {
        Self { next_id: 1 }
    }

    pub fn next(&mut self) -> EntityId {
        let id = EntityId(self.next_id);
        self.next_id += 1;
        id
    }

    /// Reset to a specific ID (for rollback/deserialization).
    pub fn reset_to(&mut self, id: u32) {
        self.next_id = id;
    }
}
