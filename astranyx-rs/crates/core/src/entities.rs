//! Entity types and management for the simulation.
//!
//! Uses a simple array-based entity storage for deterministic iteration order.
//! No hashmaps or sets - iteration order must be identical across all clients.

use bincode::{Decode, Encode};
use glam::{Vec2, Vec3};
use serde::{Deserialize, Serialize};

use crate::level::GameMode;

/// Unique identifier for an entity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Encode, Decode)]
pub struct EntityId(pub u32);

/// Player ship entity.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct Player {
    pub id: EntityId,

    // 2D position/velocity (used for side-scroll mode)
    #[bincode(with_serde)]
    pub position: Vec2,
    #[bincode(with_serde)]
    pub velocity: Vec2,
    pub rotation: f32, // 2D rotation in radians

    // 3D position/velocity (used for FPS, on-rails, free-flight modes)
    #[bincode(with_serde)]
    pub position_3d: Vec3,
    #[bincode(with_serde)]
    pub velocity_3d: Vec3,

    // FPS look angles (in radians)
    pub look_yaw: f32,   // Horizontal rotation around Y axis
    pub look_pitch: f32, // Vertical rotation around X axis

    // Combat stats
    pub health: i32,
    pub max_health: i32,
    pub invincibility_frames: u32,
    pub fire_cooldown: u32,
    pub special_charge: f32,
}

impl Player {
    // Movement speeds
    pub const SPEED: f32 = 200.0;        // 2D movement speed
    pub const FOCUS_SPEED: f32 = 80.0;   // 2D focus/precision mode speed
    pub const FPS_SPEED: f32 = 100.0;    // FPS movement speed
    pub const FPS_RUN_SPEED: f32 = 180.0; // FPS sprint speed

    // Combat
    pub const FIRE_RATE: u32 = 6; // Frames between shots
    pub const HITBOX_RADIUS: f32 = 4.0;

    // Look limits
    pub const MAX_PITCH: f32 = 1.4; // ~80 degrees up/down

    pub fn new(id: EntityId, position: Vec2) -> Self {
        Self {
            id,
            position,
            velocity: Vec2::ZERO,
            rotation: 0.0,
            position_3d: Vec3::new(position.x, 0.0, position.y),
            velocity_3d: Vec3::ZERO,
            look_yaw: 0.0,
            look_pitch: 0.0,
            health: 3,
            max_health: 3,
            invincibility_frames: 0,
            fire_cooldown: 0,
            special_charge: 0.0,
        }
    }

    /// Create a player at a 3D position (for FPS modes).
    pub fn new_3d(id: EntityId, position: Vec3) -> Self {
        Self {
            id,
            position: Vec2::new(position.x, position.z),
            velocity: Vec2::ZERO,
            rotation: 0.0,
            position_3d: position,
            velocity_3d: Vec3::ZERO,
            look_yaw: 0.0,
            look_pitch: 0.0,
            health: 3,
            max_health: 3,
            invincibility_frames: 0,
            fire_cooldown: 0,
            special_charge: 0.0,
        }
    }

    /// Get the effective position based on game mode.
    pub fn effective_position(&self, mode: &GameMode) -> Vec3 {
        if mode.is_2d() {
            Vec3::new(self.position.x, self.position.y, 0.0)
        } else {
            self.position_3d
        }
    }

    /// Get the forward direction vector in 3D (for FPS/free-flight).
    pub fn forward_3d(&self) -> Vec3 {
        let cos_pitch = self.look_pitch.cos();
        Vec3::new(
            self.look_yaw.sin() * cos_pitch,
            -self.look_pitch.sin(),
            self.look_yaw.cos() * cos_pitch,
        )
    }

    /// Get the right direction vector in 3D (for strafing).
    pub fn right_3d(&self) -> Vec3 {
        Vec3::new(self.look_yaw.cos(), 0.0, -self.look_yaw.sin())
    }

    /// Get the flat forward direction (ignoring pitch, for ground movement).
    pub fn forward_flat(&self) -> Vec3 {
        Vec3::new(self.look_yaw.sin(), 0.0, self.look_yaw.cos()).normalize_or_zero()
    }

    /// Set position for segment transition.
    pub fn set_position_3d(&mut self, pos: Vec3) {
        self.position_3d = pos;
        self.position = Vec2::new(pos.x, pos.z);
    }

    /// Sync 2D and 3D positions (call after 2D updates to keep 3D in sync).
    pub fn sync_2d_to_3d(&mut self) {
        self.position_3d.x = self.position.x;
        self.position_3d.z = self.position.y;
    }

    /// Sync 3D position back to 2D (call after 3D updates).
    pub fn sync_3d_to_2d(&mut self) {
        self.position.x = self.position_3d.x;
        self.position.y = self.position_3d.z;
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

/// Enemy type - matches script file names in scripts/enemies/
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Encode, Decode)]
pub enum EnemyType {
    // Original types (mapped to scripts)
    Basic,  // -> grunt
    Fast,   // -> speeder
    Heavy,  // -> tank
    Boss,   // -> (handled separately)
    // New script-based types
    Grunt,
    Shooter,
    Swerver,
    Tank,
    Speeder,
    Bomber,
    Sniper,
    Carrier,
    Mine,
    Spiral,
    Shield,
    Splitter,
}

impl EnemyType {
    /// Get the script name for this enemy type.
    pub fn script_name(&self) -> &'static str {
        match self {
            EnemyType::Basic | EnemyType::Grunt => "grunt",
            EnemyType::Shooter => "shooter",
            EnemyType::Swerver => "swerver",
            EnemyType::Heavy | EnemyType::Tank => "tank",
            EnemyType::Fast | EnemyType::Speeder => "speeder",
            EnemyType::Bomber => "bomber",
            EnemyType::Sniper => "sniper",
            EnemyType::Carrier => "carrier",
            EnemyType::Mine => "mine",
            EnemyType::Spiral => "spiral",
            EnemyType::Shield => "shield",
            EnemyType::Splitter => "splitter",
            EnemyType::Boss => "grunt", // Bosses handled separately
        }
    }

    /// Create from script name.
    pub fn from_script_name(name: &str) -> Self {
        match name {
            "grunt" => EnemyType::Grunt,
            "shooter" => EnemyType::Shooter,
            "swerver" => EnemyType::Swerver,
            "tank" => EnemyType::Tank,
            "speeder" => EnemyType::Speeder,
            "bomber" => EnemyType::Bomber,
            "sniper" => EnemyType::Sniper,
            "carrier" => EnemyType::Carrier,
            "mine" => EnemyType::Mine,
            "spiral" => EnemyType::Spiral,
            "shield" => EnemyType::Shield,
            "splitter" => EnemyType::Splitter,
            _ => EnemyType::Grunt,
        }
    }
}

impl Enemy {
    pub fn new(id: EntityId, position: Vec2, enemy_type: EnemyType) -> Self {
        let health = match enemy_type {
            EnemyType::Basic | EnemyType::Grunt => 20,
            EnemyType::Shooter => 40,
            EnemyType::Swerver => 25,
            EnemyType::Heavy | EnemyType::Tank => 150,
            EnemyType::Fast | EnemyType::Speeder => 15,
            EnemyType::Bomber => 60,
            EnemyType::Sniper => 50,
            EnemyType::Carrier => 120,
            EnemyType::Mine => 30,
            EnemyType::Spiral => 70,
            EnemyType::Shield => 100,
            EnemyType::Splitter => 80,
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
            EnemyType::Basic | EnemyType::Grunt => 16.0,
            EnemyType::Shooter => 18.0,
            EnemyType::Swerver => 16.0,
            EnemyType::Heavy | EnemyType::Tank => 28.0,
            EnemyType::Fast | EnemyType::Speeder => 14.0,
            EnemyType::Bomber => 20.0,
            EnemyType::Sniper => 18.0,
            EnemyType::Carrier => 26.0,
            EnemyType::Mine => 20.0,
            EnemyType::Spiral => 20.0,
            EnemyType::Shield => 24.0,
            EnemyType::Splitter => 22.0,
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
