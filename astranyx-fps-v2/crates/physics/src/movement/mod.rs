//! Player movement physics system.
//!
//! This module implements Quake-style FPS movement with:
//!
//! - Ground and air movement with different physics
//! - Friction and acceleration models
//! - Jumping, crouching, and sprinting
//! - Multi-plane collision sliding
//! - Stair stepping
//!
//! # Design
//!
//! Movement is controlled by the [`PlayerController`] which takes input commands
//! and updates the player's [`MovementState`] through the collision world.
//!
//! All movement is deterministic - the same inputs will always produce the same
//! outputs, making it suitable for lockstep multiplayer.

mod config;
mod controller;
mod slide_move;
mod state;

pub use config::MovementConfig;
pub use controller::PlayerController;
pub use state::{CommandButtons, MovementFlags, MovementState, PlayerCommand};
