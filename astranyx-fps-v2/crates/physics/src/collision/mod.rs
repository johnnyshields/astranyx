//! Collision detection system for FPS movement.
//!
//! This module provides world collision testing using capsule and box shapes.
//! Based on Quake/Daemon's collision system but simplified for modern use.
//!
//! # Key Types
//!
//! - [`CollisionWorld`]: The collision environment containing all geometry
//! - [`TraceResult`]: Output from a collision trace
//! - [`TraceShape`]: Shape used for tracing (capsule or box)
//!
//! # Tracing Algorithm
//!
//! Traces sweep a shape through the world and return:
//! - How far the shape traveled (fraction 0.0-1.0)
//! - The final position
//! - Surface normal at impact (if any)
//! - Content flags of what was hit

mod flags;
mod trace;
mod world;

pub use flags::{ContentFlags, SurfaceFlags};
pub use trace::{TraceResult, TraceShape};
pub use world::CollisionWorld;
