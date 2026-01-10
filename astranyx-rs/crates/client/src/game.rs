//! Game state and rendering helpers.
//!
//! Provides mesh names, colors, and rendering info lookups.

use glam::Vec4;

use astranyx_core::entities::{Enemy, EnemyType, PowerUp, PowerUpType, Projectile, ProjectileType};

/// Mesh names for each entity type.
pub mod mesh_names {
    pub const PLAYER_SHIP: &str = "player_ship";
    pub const ENEMY_BASIC: &str = "enemy_basic";
    pub const ENEMY_FAST: &str = "enemy_fast";
    pub const ENEMY_HEAVY: &str = "enemy_heavy";
    pub const ENEMY_BOSS: &str = "enemy_boss";
    pub const BULLET_PLAYER: &str = "bullet_player";
    pub const BULLET_ENEMY: &str = "bullet_enemy";
    pub const MISSILE: &str = "missile";
    pub const LASER: &str = "laser";
    pub const POWERUP_HEALTH: &str = "powerup_health";
    pub const POWERUP_WEAPON: &str = "powerup_weapon";
    pub const POWERUP_SPECIAL: &str = "powerup_special";
    pub const POWERUP_SHIELD: &str = "powerup_shield";
    pub const POWERUP_SPEED: &str = "powerup_speed";
}

/// Colors for different entity types.
pub mod colors {
    use glam::Vec4;

    pub const PLAYER: Vec4 = Vec4::new(0.2, 0.6, 1.0, 1.0); // Blue
    pub const PLAYER_INVINCIBLE: Vec4 = Vec4::new(1.0, 1.0, 1.0, 0.5); // White transparent

    pub const ENEMY_BASIC: Vec4 = Vec4::new(0.8, 0.2, 0.2, 1.0); // Red
    pub const ENEMY_FAST: Vec4 = Vec4::new(1.0, 0.5, 0.0, 1.0); // Orange
    pub const ENEMY_HEAVY: Vec4 = Vec4::new(0.5, 0.5, 0.5, 1.0); // Gray
    pub const ENEMY_BOSS: Vec4 = Vec4::new(0.8, 0.0, 0.8, 1.0); // Purple

    pub const BULLET_PLAYER: Vec4 = Vec4::new(0.0, 1.0, 1.0, 1.0); // Cyan
    pub const BULLET_ENEMY: Vec4 = Vec4::new(1.0, 0.3, 0.3, 1.0); // Light red
    pub const MISSILE: Vec4 = Vec4::new(1.0, 0.8, 0.0, 1.0); // Yellow
    pub const LASER: Vec4 = Vec4::new(1.0, 0.0, 0.5, 1.0); // Magenta

    pub const POWERUP_HEALTH: Vec4 = Vec4::new(0.0, 1.0, 0.0, 1.0); // Green
    pub const POWERUP_WEAPON: Vec4 = Vec4::new(1.0, 0.5, 0.0, 1.0); // Orange
    pub const POWERUP_SPECIAL: Vec4 = Vec4::new(1.0, 1.0, 0.0, 1.0); // Yellow
    pub const POWERUP_SHIELD: Vec4 = Vec4::new(0.0, 0.5, 1.0, 1.0); // Light blue
    pub const POWERUP_SPEED: Vec4 = Vec4::new(0.5, 0.0, 1.0, 1.0); // Purple
}

/// Get render info for an enemy: (mesh_name, color, scale).
pub fn get_enemy_render_info(enemy: &Enemy) -> (&'static str, Vec4, f32) {
    match enemy.enemy_type {
        // Basic/Grunt - standard red enemy
        EnemyType::Basic | EnemyType::Grunt | EnemyType::Shooter | EnemyType::Swerver => {
            (mesh_names::ENEMY_BASIC, colors::ENEMY_BASIC, 25.0)
        }
        // Fast types - orange drones
        EnemyType::Fast | EnemyType::Speeder | EnemyType::Bomber => {
            (mesh_names::ENEMY_FAST, colors::ENEMY_FAST, 20.0)
        }
        // Heavy types - gray tanks
        EnemyType::Heavy | EnemyType::Tank | EnemyType::Carrier | EnemyType::Shield => {
            (mesh_names::ENEMY_HEAVY, colors::ENEMY_HEAVY, 40.0)
        }
        // Special types
        EnemyType::Sniper => (mesh_names::ENEMY_BASIC, colors::ENEMY_FAST, 22.0),
        EnemyType::Mine => (mesh_names::ENEMY_BASIC, colors::ENEMY_HEAVY, 20.0),
        EnemyType::Spiral => (mesh_names::ENEMY_FAST, colors::ENEMY_BOSS, 24.0),
        EnemyType::Splitter => (mesh_names::ENEMY_BASIC, colors::ENEMY_BOSS, 28.0),
        // Boss
        EnemyType::Boss => (mesh_names::ENEMY_BOSS, colors::ENEMY_BOSS, 80.0),
    }
}

/// Get render info for a projectile: (mesh_name, color, scale).
pub fn get_projectile_render_info(proj: &Projectile) -> (&'static str, Vec4, f32) {
    match proj.projectile_type {
        ProjectileType::PlayerBullet => (mesh_names::BULLET_PLAYER, colors::BULLET_PLAYER, 15.0),
        ProjectileType::PlayerMissile => (mesh_names::MISSILE, colors::MISSILE, 20.0),
        ProjectileType::EnemyBullet => (mesh_names::BULLET_ENEMY, colors::BULLET_ENEMY, 12.0),
        ProjectileType::EnemyLaser => (mesh_names::LASER, colors::LASER, 10.0),
    }
}

/// Get render info for a power-up: (mesh_name, color).
pub fn get_powerup_render_info(power_up: &PowerUp) -> (&'static str, Vec4) {
    match power_up.power_type {
        PowerUpType::Health => (mesh_names::POWERUP_HEALTH, colors::POWERUP_HEALTH),
        PowerUpType::Weapon => (mesh_names::POWERUP_WEAPON, colors::POWERUP_WEAPON),
        PowerUpType::Special => (mesh_names::POWERUP_SPECIAL, colors::POWERUP_SPECIAL),
        PowerUpType::Shield => (mesh_names::POWERUP_SHIELD, colors::POWERUP_SHIELD),
        PowerUpType::Speed => (mesh_names::POWERUP_SPEED, colors::POWERUP_SPEED),
    }
}
