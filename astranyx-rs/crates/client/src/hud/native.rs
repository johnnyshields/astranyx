//! Native HUD implementation (placeholder).
//!
//! For native builds, we could use:
//! - wgpu_glyph for text rendering
//! - Custom 2D rendering with wgpu
//! - egui overlay
//!
//! For now, this is a stub that does nothing.

use super::{Hud, HudGameState, HudPlayerState, WeaponSlot};

/// Native HUD (currently a no-op placeholder).
pub struct NativeHud {
    _width: u32,
    _height: u32,
}

impl Default for NativeHud {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeHud {
    pub fn new() -> Self {
        Self {
            _width: 0,
            _height: 0,
        }
    }
}

impl Hud for NativeHud {
    fn init(&mut self) {
        // TODO: Initialize native text rendering (e.g., wgpu_glyph)
        tracing::info!("Native HUD initialized (placeholder)");
    }

    fn resize(&mut self, width: u32, height: u32) {
        self._width = width;
        self._height = height;
    }

    fn clear(&mut self) {
        // No-op for now
    }

    fn render_player_state(&mut self, _state: &HudPlayerState) {
        // TODO: Implement native text/shape rendering
    }

    fn render_game_state(&mut self, _state: &HudGameState) {
        // TODO: Implement native text/shape rendering
    }

    fn render_weapon_slots(&mut self, _slots: &[WeaponSlot], _active_index: usize) {
        // TODO: Implement native text/shape rendering
    }

    fn render_health_bar(&mut self, _screen_x: f32, _screen_y: f32, _health: f32, _max_health: f32, _width: f32) {
        // TODO: Implement native shape rendering
    }

    fn render_weapon_label(&mut self, _screen_x: f32, _screen_y: f32, _name: &str, _color: [f32; 4]) {
        // TODO: Implement native text rendering
    }
}
