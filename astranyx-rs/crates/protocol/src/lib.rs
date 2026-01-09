//! Network protocol for Astranyx.
//!
//! Defines all message types exchanged between peers during gameplay.
//! Uses binary encoding for minimal bandwidth usage.

pub mod messages;
pub mod codec;

pub use messages::*;
pub use codec::*;
