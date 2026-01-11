//! Player input types for the simulation.
//!
//! Inputs are collected each frame and exchanged between peers in lockstep.
//! Mouse input is quantized to i16 for determinism.

use bincode::{Decode, Encode};
use serde::{Deserialize, Serialize};

/// Bitflags for player input state.
/// Packed into a single u16 for efficient network transmission.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize, Encode, Decode)]
pub struct PlayerInput {
    /// Raw bitfield of pressed inputs
    pub bits: u16,

    /// Mouse X delta (quantized for determinism).
    /// Range: -32768 to 32767, scaled by 1000.0
    pub mouse_dx: i16,

    /// Mouse Y delta (quantized for determinism).
    /// Range: -32768 to 32767, scaled by 1000.0
    pub mouse_dy: i16,
}

impl PlayerInput {
    // Input bit positions - movement
    pub const UP: u16 = 1 << 0;
    pub const DOWN: u16 = 1 << 1;
    pub const LEFT: u16 = 1 << 2;
    pub const RIGHT: u16 = 1 << 3;

    // Actions
    pub const FIRE: u16 = 1 << 4;
    pub const SPECIAL: u16 = 1 << 5;
    pub const FOCUS: u16 = 1 << 6; // Slow movement / precision mode

    // FPS-specific movement (W/S for forward/backward)
    pub const FORWARD: u16 = 1 << 7;  // W key in FPS mode
    pub const BACKWARD: u16 = 1 << 8; // S key in FPS mode

    // Menu/cutscene
    pub const SKIP: u16 = 1 << 9; // Skip cutscene

    pub const fn new() -> Self {
        Self {
            bits: 0,
            mouse_dx: 0,
            mouse_dy: 0,
        }
    }

    pub const fn from_bits(bits: u16) -> Self {
        Self {
            bits,
            mouse_dx: 0,
            mouse_dy: 0,
        }
    }

    /// Create input with mouse delta.
    pub const fn with_mouse(bits: u16, mouse_dx: i16, mouse_dy: i16) -> Self {
        Self {
            bits,
            mouse_dx,
            mouse_dy,
        }
    }

    /// Quantize a raw mouse delta (in pixels) to i16.
    /// Multiply by 1000 to preserve precision, clamp to i16 range.
    pub fn quantize_mouse_delta(raw_delta: f32) -> i16 {
        (raw_delta * 1000.0).clamp(-32768.0, 32767.0) as i16
    }

    /// Get mouse delta as radians for FPS aiming.
    /// Applies sensitivity scaling.
    pub fn mouse_delta_radians(&self, sensitivity: f32) -> (f32, f32) {
        let dx = (self.mouse_dx as f32 / 1000.0) * sensitivity;
        let dy = (self.mouse_dy as f32 / 1000.0) * sensitivity;
        (dx, dy)
    }

    /// Set mouse delta from raw pixel values.
    pub fn set_mouse_delta(&mut self, dx: f32, dy: f32) {
        self.mouse_dx = Self::quantize_mouse_delta(dx);
        self.mouse_dy = Self::quantize_mouse_delta(dy);
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

    #[inline]
    pub const fn forward(&self) -> bool {
        self.is_pressed(Self::FORWARD)
    }

    #[inline]
    pub const fn backward(&self) -> bool {
        self.is_pressed(Self::BACKWARD)
    }

    #[inline]
    pub const fn skip(&self) -> bool {
        self.is_pressed(Self::SKIP)
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

    #[test]
    fn mouse_quantization() {
        // Test quantization preserves precision
        let raw = 5.5;
        let quantized = PlayerInput::quantize_mouse_delta(raw);
        assert_eq!(quantized, 5500);

        // Test dequantization
        let input = PlayerInput::with_mouse(0, 5500, -3000);
        let (dx, dy) = input.mouse_delta_radians(1.0);
        assert!((dx - 5.5).abs() < 0.01);
        assert!((dy - (-3.0)).abs() < 0.01);
    }

    #[test]
    fn mouse_clamping() {
        // Test extreme values are clamped
        let huge = PlayerInput::quantize_mouse_delta(100000.0);
        assert_eq!(huge, 32767);

        let tiny = PlayerInput::quantize_mouse_delta(-100000.0);
        assert_eq!(tiny, -32768);
    }

    #[test]
    fn fps_inputs() {
        let mut input = PlayerInput::new();
        assert!(!input.forward());
        assert!(!input.backward());
        assert!(!input.skip());

        input.set(PlayerInput::FORWARD, true);
        input.set(PlayerInput::SKIP, true);
        assert!(input.forward());
        assert!(input.skip());
        assert!(!input.backward());
    }
}
