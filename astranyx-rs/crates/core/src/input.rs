//! Player input types for the simulation.
//!
//! Inputs are collected each frame and exchanged between peers in lockstep.

use bincode::{Decode, Encode};
use serde::{Deserialize, Serialize};

/// Bitflags for player input state.
/// Packed into a single u16 for efficient network transmission.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize, Encode, Decode)]
pub struct PlayerInput {
    /// Raw bitfield of pressed inputs
    pub bits: u16,
}

impl PlayerInput {
    // Input bit positions
    pub const UP: u16 = 1 << 0;
    pub const DOWN: u16 = 1 << 1;
    pub const LEFT: u16 = 1 << 2;
    pub const RIGHT: u16 = 1 << 3;
    pub const FIRE: u16 = 1 << 4;
    pub const SPECIAL: u16 = 1 << 5;
    pub const FOCUS: u16 = 1 << 6; // Slow movement / precision mode

    pub const fn new() -> Self {
        Self { bits: 0 }
    }

    pub const fn from_bits(bits: u16) -> Self {
        Self { bits }
    }

    #[inline]
    pub const fn is_pressed(&self, input: u16) -> bool {
        self.bits & input != 0
    }

    #[inline]
    pub fn set(&mut self, input: u16, pressed: bool) {
        if pressed {
            self.bits |= input;
        } else {
            self.bits &= !input;
        }
    }

    #[inline]
    pub const fn up(&self) -> bool {
        self.is_pressed(Self::UP)
    }

    #[inline]
    pub const fn down(&self) -> bool {
        self.is_pressed(Self::DOWN)
    }

    #[inline]
    pub const fn left(&self) -> bool {
        self.is_pressed(Self::LEFT)
    }

    #[inline]
    pub const fn right(&self) -> bool {
        self.is_pressed(Self::RIGHT)
    }

    #[inline]
    pub const fn fire(&self) -> bool {
        self.is_pressed(Self::FIRE)
    }

    #[inline]
    pub const fn special(&self) -> bool {
        self.is_pressed(Self::SPECIAL)
    }

    #[inline]
    pub const fn focus(&self) -> bool {
        self.is_pressed(Self::FOCUS)
    }

    /// Returns horizontal axis as -1, 0, or 1.
    pub const fn horizontal(&self) -> i8 {
        match (self.left(), self.right()) {
            (true, false) => -1,
            (false, true) => 1,
            _ => 0,
        }
    }

    /// Returns vertical axis as -1, 0, or 1.
    pub const fn vertical(&self) -> i8 {
        match (self.up(), self.down()) {
            (true, false) => -1,
            (false, true) => 1,
            _ => 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn input_flags() {
        let mut input = PlayerInput::new();
        assert!(!input.fire());

        input.set(PlayerInput::FIRE, true);
        assert!(input.fire());
        assert!(!input.up());

        input.set(PlayerInput::UP, true);
        assert!(input.fire());
        assert!(input.up());

        input.set(PlayerInput::FIRE, false);
        assert!(!input.fire());
        assert!(input.up());
    }

    #[test]
    fn axis_values() {
        let mut input = PlayerInput::new();
        assert_eq!(input.horizontal(), 0);
        assert_eq!(input.vertical(), 0);

        input.set(PlayerInput::LEFT, true);
        assert_eq!(input.horizontal(), -1);

        input.set(PlayerInput::RIGHT, true);
        // Both pressed = cancel out
        assert_eq!(input.horizontal(), 0);

        input.set(PlayerInput::LEFT, false);
        assert_eq!(input.horizontal(), 1);
    }
}
