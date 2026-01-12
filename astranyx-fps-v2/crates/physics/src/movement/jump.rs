//! Jump state management.
//!
//! Handles jump cooldown and jump queuing. When the player presses jump
//! during cooldown, the jump is queued and executes automatically when
//! the cooldown ends and the player is on the ground.

use serde::{Deserialize, Serialize};

/// Default jump cooldown in milliseconds.
/// This prevents bunny hopping by requiring a delay between jumps.
pub const DEFAULT_JUMP_COOLDOWN_MS: u32 = 400;

/// How long a queued jump remains valid (ms).
/// If the player doesn't land within this time, the queued jump is discarded.
pub const JUMP_QUEUE_TIMEOUT_MS: u32 = 500;

/// Jump state machine.
///
/// Tracks cooldown timing and queued jumps for responsive, predictable jumping.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JumpState {
    /// Time remaining on jump cooldown (ms). Can't jump while > 0.
    cooldown_ms: u32,

    /// Whether a jump is queued (player pressed jump during cooldown).
    queued: bool,

    /// Time remaining for queued jump to be valid (ms).
    queue_timeout_ms: u32,

    /// Previous frame's jump input (for edge detection).
    prev_jump_pressed: bool,
}

impl Default for JumpState {
    fn default() -> Self {
        Self {
            cooldown_ms: 0,
            queued: false,
            queue_timeout_ms: 0,
            prev_jump_pressed: false,
        }
    }
}

/// Result of updating jump state.
#[derive(Debug, Clone, Copy)]
pub struct JumpUpdateResult {
    /// Whether a jump should be executed this frame.
    pub should_jump: bool,
}

impl JumpState {
    /// Create a new jump state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Update jump state for this frame.
    ///
    /// # Arguments
    ///
    /// * `jump_pressed` - Whether the jump key is currently pressed
    /// * `on_ground` - Whether the player is currently on the ground
    /// * `cooldown_setting` - Jump cooldown duration in ms (from config)
    /// * `auto_bhop` - If true, holding jump will auto-jump on each landing
    /// * `delta_time_ms` - Time since last frame in milliseconds
    ///
    /// # Returns
    ///
    /// Whether a jump should be executed this frame.
    pub fn update(
        &mut self,
        jump_pressed: bool,
        on_ground: bool,
        cooldown_setting: u32,
        auto_bhop: bool,
        delta_time_ms: u32,
    ) -> JumpUpdateResult {
        // Detect key edge
        let jump_just_pressed = jump_pressed && !self.prev_jump_pressed;
        self.prev_jump_pressed = jump_pressed;

        // Update timers
        self.cooldown_ms = self.cooldown_ms.saturating_sub(delta_time_ms);
        self.queue_timeout_ms = self.queue_timeout_ms.saturating_sub(delta_time_ms);

        // Clear queued jump if timeout expired
        if self.queue_timeout_ms == 0 {
            self.queued = false;
        }

        // Check if we should execute a jump
        let can_jump = on_ground && self.cooldown_ms == 0;

        // Queue jump if pressed during cooldown or while airborne
        if jump_just_pressed && !can_jump {
            self.queued = true;
            self.queue_timeout_ms = JUMP_QUEUE_TIMEOUT_MS;
        }

        // Execute jump if:
        // 1. Jump was just pressed and we can jump, OR
        // 2. A jump is queued and we can now jump, OR
        // 3. Auto-bhop is enabled and jump is held and we can jump
        let should_jump = can_jump && (jump_just_pressed || self.queued || (auto_bhop && jump_pressed));

        if should_jump {
            // Start cooldown and clear queue
            self.cooldown_ms = cooldown_setting;
            self.queued = false;
            self.queue_timeout_ms = 0;
        }

        JumpUpdateResult { should_jump }
    }

    /// Check if a jump is currently queued.
    pub fn is_queued(&self) -> bool {
        self.queued
    }

    /// Check if jump is on cooldown.
    pub fn on_cooldown(&self) -> bool {
        self.cooldown_ms > 0
    }

    /// Get remaining cooldown time in milliseconds.
    pub fn cooldown_remaining(&self) -> u32 {
        self.cooldown_ms
    }

    /// Manually clear any queued jump.
    pub fn clear_queue(&mut self) {
        self.queued = false;
        self.queue_timeout_ms = 0;
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    const COOLDOWN: u32 = 400;
    const FRAME_MS: u32 = 16; // ~60fps

    // Helper to update without auto_bhop
    fn update(state: &mut JumpState, jump: bool, ground: bool) -> JumpUpdateResult {
        state.update(jump, ground, COOLDOWN, false, FRAME_MS)
    }

    // Helper to update with auto_bhop
    fn update_bhop(state: &mut JumpState, jump: bool, ground: bool) -> JumpUpdateResult {
        state.update(jump, ground, COOLDOWN, true, FRAME_MS)
    }

    #[test]
    fn test_basic_jump() {
        let mut state = JumpState::new();

        // Press jump while on ground with no cooldown
        let result = update(&mut state, true, true);
        assert!(result.should_jump);
        assert!(state.on_cooldown());
    }

    #[test]
    fn test_cooldown_prevents_jump() {
        let mut state = JumpState::new();

        // First jump
        let result = update(&mut state, true, true);
        assert!(result.should_jump);

        // Release and press again immediately - should not jump (cooldown)
        update(&mut state, false, true);
        let result = update(&mut state, true, true);
        assert!(!result.should_jump);
    }

    #[test]
    fn test_jump_after_cooldown() {
        let mut state = JumpState::new();

        // First jump
        update(&mut state, true, true);

        // Wait for cooldown to expire
        for _ in 0..(COOLDOWN / FRAME_MS + 1) {
            update(&mut state, false, true);
        }

        // Should be able to jump again
        let result = update(&mut state, true, true);
        assert!(result.should_jump);
    }

    #[test]
    fn test_jump_queue_during_cooldown() {
        let mut state = JumpState::new();

        // First jump
        update(&mut state, true, true);

        // Release
        update(&mut state, false, true);

        // Press jump during cooldown - should queue
        let result = update(&mut state, true, true);
        assert!(!result.should_jump);
        assert!(state.is_queued());

        // Release and wait for cooldown
        for _ in 0..(COOLDOWN / FRAME_MS + 1) {
            let result = update(&mut state, false, true);
            if result.should_jump {
                // Queued jump executed!
                return;
            }
        }

        panic!("Queued jump should have executed after cooldown");
    }

    #[test]
    fn test_jump_queue_while_airborne() {
        let mut state = JumpState::new();

        // First jump
        update(&mut state, true, true);

        // In the air, release then press jump - should queue
        update(&mut state, false, false);
        let result = update(&mut state, true, false);
        assert!(!result.should_jump);
        assert!(state.is_queued());

        // Wait for cooldown while still airborne
        for _ in 0..(COOLDOWN / FRAME_MS) {
            update(&mut state, false, false);
        }

        // Land - queued jump should execute
        let result = update(&mut state, false, true);
        assert!(result.should_jump);
        assert!(!state.is_queued());
    }

    #[test]
    fn test_queue_timeout() {
        let mut state = JumpState::new();

        // Press jump while airborne (no cooldown but not on ground)
        let result = update(&mut state, true, false);
        assert!(!result.should_jump);
        assert!(state.is_queued());

        // Stay airborne for too long - queue should timeout
        for _ in 0..(JUMP_QUEUE_TIMEOUT_MS / FRAME_MS + 1) {
            update(&mut state, false, false);
        }

        assert!(!state.is_queued());

        // Landing now should NOT trigger a jump
        let result = update(&mut state, false, true);
        assert!(!result.should_jump);
    }

    #[test]
    fn test_cannot_jump_while_airborne() {
        let mut state = JumpState::new();

        // Press jump while airborne with no cooldown
        let result = update(&mut state, true, false);
        assert!(!result.should_jump);
    }

    #[test]
    fn test_holding_jump_only_triggers_once() {
        let mut state = JumpState::new();

        // Hold jump for multiple frames (without auto_bhop)
        let result = update(&mut state, true, true);
        assert!(result.should_jump);

        // Still holding - should not jump again (no auto_bhop)
        for _ in 0..10 {
            let result = update(&mut state, true, true);
            assert!(!result.should_jump);
        }
    }

    #[test]
    fn test_auto_bhop_holding_jump_keeps_jumping() {
        let mut state = JumpState::new();

        // First jump with auto_bhop
        let result = update_bhop(&mut state, true, true);
        assert!(result.should_jump);

        // Wait for cooldown to expire while still holding
        // The first jump started cooldown, so we need enough frames
        // to expire it (cooldown / frame_ms frames)
        let mut jumped_again = false;
        for _ in 0..(COOLDOWN / FRAME_MS + 5) {
            let result = update_bhop(&mut state, true, true);
            if result.should_jump {
                jumped_again = true;
                break;
            }
        }

        assert!(jumped_again, "Should have jumped again with auto_bhop while holding");
    }

    #[test]
    fn test_auto_bhop_released_does_not_jump() {
        let mut state = JumpState::new();

        // Jump and release
        update_bhop(&mut state, true, true);
        update_bhop(&mut state, false, true);

        // Wait for cooldown
        for _ in 0..(COOLDOWN / FRAME_MS + 1) {
            update_bhop(&mut state, false, true);
        }

        // Not pressing jump - should not auto-jump even with auto_bhop
        let result = update_bhop(&mut state, false, true);
        assert!(!result.should_jump);
    }
}
