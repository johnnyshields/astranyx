//! Game state and rendering bridge.
//!
//! Connects the simulation to the renderer, mapping entities to meshes.

use glam::{Vec3, Vec4};

use astranyx_core::entities::{Enemy, EnemyType, Player, PowerUp, PowerUpType, Projectile, ProjectileType};
use astranyx_core::simulation::GameState;

use crate::renderer::{meshes, MeshBuilder, Renderer};

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

    pub const PLAYER: Vec4 = Vec4::new(0.2, 0.6, 1.0, 1.0);        // Blue
    pub const PLAYER_INVINCIBLE: Vec4 = Vec4::new(1.0, 1.0, 1.0, 0.5); // White transparent

    pub const ENEMY_BASIC: Vec4 = Vec4::new(0.8, 0.2, 0.2, 1.0);   // Red
    pub const ENEMY_FAST: Vec4 = Vec4::new(1.0, 0.5, 0.0, 1.0);    // Orange
    pub const ENEMY_HEAVY: Vec4 = Vec4::new(0.5, 0.5, 0.5, 1.0);   // Gray
    pub const ENEMY_BOSS: Vec4 = Vec4::new(0.8, 0.0, 0.8, 1.0);    // Purple

    pub const BULLET_PLAYER: Vec4 = Vec4::new(0.0, 1.0, 1.0, 1.0); // Cyan
    pub const BULLET_ENEMY: Vec4 = Vec4::new(1.0, 0.3, 0.3, 1.0);  // Light red
    pub const MISSILE: Vec4 = Vec4::new(1.0, 0.8, 0.0, 1.0);       // Yellow
    pub const LASER: Vec4 = Vec4::new(1.0, 0.0, 0.5, 1.0);         // Magenta

    pub const POWERUP_HEALTH: Vec4 = Vec4::new(0.0, 1.0, 0.0, 1.0);  // Green
    pub const POWERUP_WEAPON: Vec4 = Vec4::new(1.0, 0.5, 0.0, 1.0);  // Orange
    pub const POWERUP_SPECIAL: Vec4 = Vec4::new(1.0, 1.0, 0.0, 1.0); // Yellow
    pub const POWERUP_SHIELD: Vec4 = Vec4::new(0.0, 0.5, 1.0, 1.0);  // Light blue
    pub const POWERUP_SPEED: Vec4 = Vec4::new(0.5, 0.0, 1.0, 1.0);   // Purple
}

/// Register all game meshes with the renderer.
pub fn register_meshes(renderer: &mut Renderer) {
    use mesh_names::*;

    // Player
    renderer.register_mesh(PLAYER_SHIP, &meshes::create_player_ship_mesh());

    // Enemies
    renderer.register_mesh(ENEMY_BASIC, &meshes::create_enemy_ship_mesh());
    renderer.register_mesh(ENEMY_FAST, &meshes::create_drone_mesh());
    renderer.register_mesh(ENEMY_HEAVY, &meshes::create_tank_mesh());
    renderer.register_mesh(ENEMY_BOSS, &meshes::create_boss_core_mesh());

    // Projectiles
    renderer.register_mesh(BULLET_PLAYER, &meshes::create_bullet_mesh());
    renderer.register_mesh(BULLET_ENEMY, &meshes::create_bullet_mesh());
    renderer.register_mesh(MISSILE, &meshes::create_bullet_mesh()); // TODO: missile mesh
    renderer.register_mesh(LASER, &meshes::create_laser_mesh());

    // Power-ups (all use diamond shape)
    renderer.register_mesh(POWERUP_HEALTH, &meshes::create_powerup_mesh());
    renderer.register_mesh(POWERUP_WEAPON, &meshes::create_powerup_mesh());
    renderer.register_mesh(POWERUP_SPECIAL, &meshes::create_powerup_mesh());
    renderer.register_mesh(POWERUP_SHIELD, &meshes::create_powerup_mesh());
    renderer.register_mesh(POWERUP_SPEED, &meshes::create_powerup_mesh());

    // Test box for debugging
    let mut builder = MeshBuilder::new();
    builder.add_box(1.0, 1.0, 1.0);
    renderer.register_mesh("test_box", &builder.finish());

    tracing::info!("Registered all game meshes");
}

/// Convert 2D game position to 3D world position.
/// Game uses Vec2 (X=horizontal, Y=vertical).
/// 3D uses Vec3 (X=forward, Y=up, Z=side).
///
/// For 2.5D side-scroller:
/// - Game X (horizontal) -> 3D X (forward/scroll direction)
/// - Game Y (vertical) -> 3D Y (up/down)
/// - Z = 0 for main game plane
fn game_to_world(pos: glam::Vec2) -> Vec3 {
    Vec3::new(pos.x, pos.y, 0.0)
}

/// Scale factor to convert game units to world units.
/// Meshes are in -0.5 to 0.5 range, scale up for visibility.
const SCALE: f32 = 5.0;

/// Render all entities from the game state.
pub fn render_game_state(
    renderer: &mut Renderer,
    state: &GameState,
    encoder: &mut wgpu::CommandEncoder,
    view: &wgpu::TextureView,
) {
    let time = renderer.time();

    // Render players
    for player in &state.players {
        render_player(renderer, player, time, encoder, view);
    }

    // Render enemies
    for enemy in &state.enemies {
        render_enemy(renderer, enemy, time, encoder, view);
    }

    // Render projectiles
    for projectile in &state.projectiles {
        render_projectile(renderer, projectile, time, encoder, view);
    }

    // Render power-ups
    for power_up in &state.power_ups {
        render_powerup(renderer, power_up, time, encoder, view);
    }
}

fn render_player(
    renderer: &mut Renderer,
    player: &Player,
    time: f32,
    encoder: &mut wgpu::CommandEncoder,
    view: &wgpu::TextureView,
) {
    if !player.is_alive() {
        return;
    }

    let pos = game_to_world(player.position);
    let scale = Vec3::splat(30.0 * SCALE);

    // Blink when invincible
    let color = if player.is_invincible() {
        let blink = ((time * 10.0).sin() > 0.0) as u8 as f32;
        Vec4::new(
            colors::PLAYER_INVINCIBLE.x,
            colors::PLAYER_INVINCIBLE.y,
            colors::PLAYER_INVINCIBLE.z,
            0.3 + blink * 0.5,
        )
    } else {
        colors::PLAYER
    };

    // Slight banking based on vertical velocity
    let bank = -player.velocity.y * 0.002;
    let rotation = Vec3::new(0.0, 0.0, bank);

    renderer.draw_mesh(
        mesh_names::PLAYER_SHIP,
        pos,
        scale,
        rotation,
        color,
        encoder,
        view,
    );
}

fn render_enemy(
    renderer: &mut Renderer,
    enemy: &Enemy,
    _time: f32,
    encoder: &mut wgpu::CommandEncoder,
    view: &wgpu::TextureView,
) {
    if !enemy.is_alive() {
        return;
    }

    let pos = game_to_world(enemy.position);

    let (mesh_name, color, base_scale) = match enemy.enemy_type {
        EnemyType::Basic => (mesh_names::ENEMY_BASIC, colors::ENEMY_BASIC, 25.0),
        EnemyType::Fast => (mesh_names::ENEMY_FAST, colors::ENEMY_FAST, 20.0),
        EnemyType::Heavy => (mesh_names::ENEMY_HEAVY, colors::ENEMY_HEAVY, 40.0),
        EnemyType::Boss => (mesh_names::ENEMY_BOSS, colors::ENEMY_BOSS, 80.0),
    };

    let scale = Vec3::splat(base_scale * SCALE);
    let rotation = Vec3::ZERO;

    renderer.draw_mesh(mesh_name, pos, scale, rotation, color, encoder, view);
}

fn render_projectile(
    renderer: &mut Renderer,
    projectile: &Projectile,
    _time: f32,
    encoder: &mut wgpu::CommandEncoder,
    view: &wgpu::TextureView,
) {
    let pos = game_to_world(projectile.position);

    let (mesh_name, color, base_scale) = match projectile.projectile_type {
        ProjectileType::PlayerBullet => (mesh_names::BULLET_PLAYER, colors::BULLET_PLAYER, 15.0),
        ProjectileType::PlayerMissile => (mesh_names::MISSILE, colors::MISSILE, 20.0),
        ProjectileType::EnemyBullet => (mesh_names::BULLET_ENEMY, colors::BULLET_ENEMY, 12.0),
        ProjectileType::EnemyLaser => (mesh_names::LASER, colors::LASER, 10.0),
    };

    let scale = Vec3::splat(base_scale * SCALE);

    // Point projectile in direction of travel
    let rotation = if projectile.velocity.length_squared() > 0.0 {
        let angle = projectile.velocity.y.atan2(projectile.velocity.x);
        Vec3::new(0.0, 0.0, angle)
    } else {
        Vec3::ZERO
    };

    renderer.draw_mesh(mesh_name, pos, scale, rotation, color, encoder, view);
}

fn render_powerup(
    renderer: &mut Renderer,
    power_up: &PowerUp,
    time: f32,
    encoder: &mut wgpu::CommandEncoder,
    view: &wgpu::TextureView,
) {
    let pos = game_to_world(power_up.position);

    let (mesh_name, color) = match power_up.power_type {
        PowerUpType::Health => (mesh_names::POWERUP_HEALTH, colors::POWERUP_HEALTH),
        PowerUpType::Weapon => (mesh_names::POWERUP_WEAPON, colors::POWERUP_WEAPON),
        PowerUpType::Special => (mesh_names::POWERUP_SPECIAL, colors::POWERUP_SPECIAL),
        PowerUpType::Shield => (mesh_names::POWERUP_SHIELD, colors::POWERUP_SHIELD),
        PowerUpType::Speed => (mesh_names::POWERUP_SPEED, colors::POWERUP_SPEED),
    };

    // Pulsing scale
    let pulse = 1.0 + (time * 3.0).sin() * 0.1;
    let scale = Vec3::splat(20.0 * SCALE * pulse);

    // Spinning
    let rotation = Vec3::new(0.0, time * 2.0, time * 1.5);

    renderer.draw_mesh(mesh_name, pos, scale, rotation, color, encoder, view);
}
