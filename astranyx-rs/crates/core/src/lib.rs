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

pub mod random;
pub mod simulation;
pub mod entities;
pub mod physics;
pub mod input;

pub use random::SeededRandom;
pub use simulation::{Simulation, SimulationConfig};
pub use input::PlayerInput;
