//! Astranyx Physics Engine
//!
//! A deterministic FPS physics engine inspired by Quake/Daemon, designed for
//! lockstep multiplayer. All calculations use fixed-point semantics where possible
//! to ensure identical results across clients.
//!
//! # Architecture
//!
//! The physics engine is split into two main systems:
//!
//! - **Collision**: Traces capsules/boxes through the world, returns hit information
//! - **Movement**: Uses collision traces to implement player movement physics
//!
//! # Design Principles
//!
//! 1. **Determinism**: Same inputs always produce same outputs across platforms
//! 2. **Simplicity**: Clean APIs over micro-optimizations
//! 3. **Accuracy**: Proper capsule collision for smooth movement
//! 4. **Performance**: Efficient enough for 60Hz simulation

pub mod collision;
pub mod movement;

// Re-export commonly used types
pub use collision::{
    CollisionWorld, ContentFlags, SurfaceFlags, TraceResult, TraceShape,
};
pub use movement::{
    CommandButtons, MovementConfig, MovementFlags, MovementState, PlayerCommand, PlayerController,
};
