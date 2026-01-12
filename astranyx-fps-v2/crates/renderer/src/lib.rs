//! Astranyx Renderer
//!
//! A three-d based PBR renderer for the Astranyx FPS game.
//!
//! # Features
//!
//! - PBR (Physically Based Rendering) materials
//! - glTF level loading with `_col` collision mesh convention
//! - Dynamic lighting
//! - First-person camera
//!
//! # Usage
//!
//! The renderer is designed to be driven by game state from `astranyx-game`.
//! Each frame, update the renderer with the current game state and call render.

pub mod camera;

/// Placeholder for the game renderer.
///
/// Will be implemented using three-d for PBR rendering.
pub struct GameRenderer {
    // TODO: three-d context, meshes, lights, etc.
}

impl GameRenderer {
    /// Create a new game renderer.
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for GameRenderer {
    fn default() -> Self {
        Self::new()
    }
}
