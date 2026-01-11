//! Astranyx FPS Game Logic
//!
//! This crate contains the core game simulation including:
//!
//! - Player state and input handling
//! - Entity management (players, enemies, projectiles)
//! - Level loading and management
//! - Game state serialization for netcode
//!
//! # Architecture
//!
//! The game uses a deterministic simulation suitable for lockstep multiplayer.
//! All state updates are driven by player input commands and a fixed timestep.
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                      Game Simulation                         │
//! │  ┌─────────┐    ┌──────────┐    ┌────────────────────────┐  │
//! │  │ Input   │───►│ Physics  │───►│ Game State             │  │
//! │  │ Commands│    │ (movement│    │ (players, enemies,     │  │
//! │  └─────────┘    │ collision)    │  projectiles, level)   │  │
//! │                 └──────────┘    └────────────────────────┘  │
//! └─────────────────────────────────────────────────────────────┘
//! ```

pub mod input;
pub mod level;
pub mod player;
pub mod simulation;

// Re-export main types
pub use input::PlayerInput;
pub use level::Level;
pub use player::Player;
pub use simulation::Simulation;

// Re-export physics types for convenience
pub use astranyx_physics::{
    CollisionWorld, ContentFlags, MovementConfig, MovementState, PlayerCommand,
    PlayerController, TraceResult, TraceShape,
};
