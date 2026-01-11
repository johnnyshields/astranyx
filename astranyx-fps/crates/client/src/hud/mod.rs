//! HUD (Heads-Up Display) rendering.
//!
//! On WASM: Uses web-sys 2D Canvas API overlay
//! On Native: Could use wgpu text rendering (not yet implemented)

/// Player state for HUD display.
#[derive(Debug, Clone, Default)]
pub struct HudPlayerState {
    pub shields: f32,
    pub max_shields: f32,
    pub lives: u32,
    pub ship_level: u32,
    pub score: u64,
    pub multiplier: f32,
    pub wave: u32,
}

/// Game state for HUD display.
#[derive(Debug, Clone, Default)]
pub struct HudGameState {
    pub boss_active: bool,
    pub boss_health: f32,
    pub boss_max_health: f32,
    pub enemy_count: u32,
}

/// Weapon slot info for HUD.
#[derive(Debug, Clone)]
pub struct WeaponSlot {
    pub name: String,
    pub ammo: u32,
    pub max_ammo: u32,
    pub color: [f32; 4],
}

/// HUD trait for platform-specific implementations.
pub trait Hud {
    /// Initialize the HUD.
    fn init(&mut self);

    /// Resize the HUD viewport.
    fn resize(&mut self, width: u32, height: u32);

    /// Clear the HUD canvas.
    fn clear(&mut self);

    /// Render player state (shields, lives, level).
    fn render_player_state(&mut self, state: &HudPlayerState);

    /// Render game state (score, wave, boss health).
    fn render_game_state(&mut self, state: &HudGameState);

    /// Render weapon slots.
    fn render_weapon_slots(&mut self, slots: &[WeaponSlot], active_index: usize);

    /// Render an entity health bar at screen position.
    fn render_health_bar(&mut self, screen_x: f32, screen_y: f32, health: f32, max_health: f32, width: f32);

    /// Render a weapon drop label at screen position.
    fn render_weapon_label(&mut self, screen_x: f32, screen_y: f32, name: &str, color: [f32; 4]);
}

#[cfg(target_arch = "wasm32")]
mod web;

#[cfg(target_arch = "wasm32")]
pub use web::WebHud;

#[cfg(not(target_arch = "wasm32"))]
mod native;

#[cfg(not(target_arch = "wasm32"))]
pub use native::NativeHud;

// Debug HUD (native only for now)
#[cfg(not(target_arch = "wasm32"))]
mod debug;

#[cfg(not(target_arch = "wasm32"))]
pub use debug::DebugHud;
