//! Astranyx Core - Deterministic Game Simulation
//!
//! This crate contains the core game simulation logic that must be
//! 100% deterministic for P2P lockstep networking to work correctly.
//!
//! # Determinism Rules
//!
//! 1. No `rand::thread_rng()` - Use `SeededRandom` only
//! 2. No system time - Use frame counter
//! 3. Careful with floats - Use fixed-point for critical paths
//! 4. Ordered iteration - `Vec` not `HashMap` for entities
//! 5. No async - Pure synchronous logic

pub mod entities;
pub mod input;
pub mod level;
pub mod physics;
pub mod random;
pub mod scripting;
pub mod simulation;

pub use input::PlayerInput;
pub use level::LevelState;
pub use physics::WorldBounds3D;
pub use random::SeededRandom;
pub use scripting::ScriptEngine;
pub use simulation::{Simulation, SimulationConfig};
