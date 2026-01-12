//! Stance state machine with toggle/hold behavior.
//!
//! Supports three stances (Standing, Crouching, Prone) with:
//! - Toggle (tap): Permanently changes base stance
//! - Hold: Temporarily lowers stance, reverts on release

use serde::{Deserialize, Serialize};

/// The three possible player stances, ordered by height (highest to lowest).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Stance {
    Standing = 0,
    Crouching = 1,
    Prone = 2,
}

impl Default for Stance {
    fn default() -> Self {
        Stance::Standing
    }
}

impl Stance {
    /// Returns true if this stance is lower than the other.
    pub fn is_lower_than(self, other: Stance) -> bool {
        (self as u8) > (other as u8)
    }

    /// Returns true if this stance is higher than the other.
    pub fn is_higher_than(self, other: Stance) -> bool {
        (self as u8) < (other as u8)
    }

    /// Get the next higher stance (Standing is highest).
    pub fn higher(self) -> Stance {
        match self {
            Stance::Standing => Stance::Standing,
            Stance::Crouching => Stance::Standing,
            Stance::Prone => Stance::Crouching,
        }
    }

    /// Get the next lower stance (Prone is lowest).
    pub fn lower(self) -> Stance {
        match self {
            Stance::Standing => Stance::Crouching,
            Stance::Crouching => Stance::Prone,
            Stance::Prone => Stance::Prone,
        }
    }
}

/// Input for stance transitions.
#[derive(Debug, Clone, Copy, Default)]
pub struct StanceInput {
    /// Crouch key is currently pressed.
    pub crouch_pressed: bool,
    /// Prone key is currently pressed.
    pub prone_pressed: bool,
    /// Jump/stand key was pressed this frame.
    pub stand_requested: bool,
    /// Delta time in milliseconds since last update.
    pub delta_time_ms: u32,
}

/// Hold threshold in milliseconds - releases before this are toggles.
const HOLD_THRESHOLD_MS: u32 = 150;

/// Stance state machine.
///
/// # How toggle vs hold works
///
/// - On key DOWN: Start hold timer, immediately go to lower stance
/// - On key UP before threshold (~150ms): Toggle - change base to new stance
/// - On key UP after threshold: Hold - revert to pre-press base stance
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StanceState {
    /// The "permanent" stance - what we return to after releasing held keys.
    pub base_stance: Stance,
    /// Current actual stance (may differ from base if holding a key).
    pub current_stance: Stance,
    /// Base stance before crouch key was pressed (for toggle detection).
    crouch_pre_press_base: Stance,
    /// Base stance before prone key was pressed (for toggle detection).
    prone_pre_press_base: Stance,
    /// The stance we should return to when hold-releasing Z (tracked when first entering prone).
    prone_hold_return_stance: Stance,
    /// Whether crouch key is currently being held down.
    crouch_active: bool,
    /// Whether prone key is currently being held down.
    prone_active: bool,
    /// How long crouch has been held (ms).
    crouch_hold_time_ms: u32,
    /// How long prone has been held (ms).
    prone_hold_time_ms: u32,
    /// Previous frame's crouch pressed state (for edge detection).
    prev_crouch_pressed: bool,
    /// Previous frame's prone pressed state (for edge detection).
    prev_prone_pressed: bool,
}

impl Default for StanceState {
    fn default() -> Self {
        Self {
            base_stance: Stance::Standing,
            current_stance: Stance::Standing,
            crouch_pre_press_base: Stance::Standing,
            prone_pre_press_base: Stance::Standing,
            prone_hold_return_stance: Stance::Standing,
            crouch_active: false,
            prone_active: false,
            crouch_hold_time_ms: 0,
            prone_hold_time_ms: 0,
            prev_crouch_pressed: false,
            prev_prone_pressed: false,
        }
    }
}

/// Result of a stance update, indicating what collision checks are needed.
#[derive(Debug, Clone, Copy)]
pub struct StanceUpdateResult {
    /// The stance we want to transition to.
    pub desired_stance: Stance,
    /// Whether we need to check if we can stand.
    pub needs_stand_check: bool,
    /// Whether we need to check if we can crouch.
    pub needs_crouch_check: bool,
}

impl StanceState {
    /// Create a new stance state starting at the given stance.
    pub fn new(stance: Stance) -> Self {
        Self {
            base_stance: stance,
            current_stance: stance,
            crouch_pre_press_base: stance,
            prone_pre_press_base: stance,
            prone_hold_return_stance: stance,
            ..Default::default()
        }
    }

    /// Update stance based on input.
    ///
    /// Returns the desired stance transition. The caller should perform collision
    /// checks and then call `apply_stance` with the actual achievable stance.
    pub fn update(&mut self, input: StanceInput) -> StanceUpdateResult {
        // Detect key edges
        let crouch_just_pressed = input.crouch_pressed && !self.prev_crouch_pressed;
        let crouch_just_released = !input.crouch_pressed && self.prev_crouch_pressed;
        let prone_just_pressed = input.prone_pressed && !self.prev_prone_pressed;
        let prone_just_released = !input.prone_pressed && self.prev_prone_pressed;

        // Update previous state for next frame
        self.prev_crouch_pressed = input.crouch_pressed;
        self.prev_prone_pressed = input.prone_pressed;

        // Update hold timers
        if self.crouch_active {
            self.crouch_hold_time_ms = self.crouch_hold_time_ms.saturating_add(input.delta_time_ms);
        }
        if self.prone_active {
            self.prone_hold_time_ms = self.prone_hold_time_ms.saturating_add(input.delta_time_ms);
        }

        // Handle stand/jump request
        // If holding a stance key, we stand temporarily (will return to held stance)
        // If not holding, we clear the toggled stance
        if input.stand_requested {
            // Only clear active states if the key is not still being held
            if !input.crouch_pressed {
                self.crouch_active = false;
                self.crouch_hold_time_ms = 0;
            }
            if !input.prone_pressed {
                self.prone_active = false;
                self.prone_hold_time_ms = 0;
            }
            // Clear base stance only if not holding any stance key
            if !input.crouch_pressed && !input.prone_pressed {
                self.base_stance = Stance::Standing;
            }
            return StanceUpdateResult {
                desired_stance: Stance::Standing,
                needs_stand_check: true,
                needs_crouch_check: false,
            };
        }

        // Handle crouch key press - save base and start timer
        // Always save pre-press so tap-toggle knows what state we were in
        if crouch_just_pressed {
            self.crouch_pre_press_base = self.base_stance;
            self.crouch_active = true;
            self.crouch_hold_time_ms = 0;
        }

        // Handle prone key press - save base and start timer
        // Always save pre-press so tap-toggle knows what state we were in
        if prone_just_pressed {
            self.prone_pre_press_base = self.base_stance;
            // If not already prone, save the return stance for hold-release
            if self.base_stance != Stance::Prone {
                self.prone_hold_return_stance = self.base_stance;
            }
            self.prone_active = true;
            self.prone_hold_time_ms = 0;
        }

        // Handle crouch key release - determine toggle vs hold based on time
        if crouch_just_released && self.crouch_active {
            self.crouch_active = false;
            let was_hold = self.crouch_hold_time_ms >= HOLD_THRESHOLD_MS;
            log::debug!(
                "crouch released: hold_time={}ms threshold={}ms was_hold={} pre_press_base={:?}",
                self.crouch_hold_time_ms, HOLD_THRESHOLD_MS, was_hold, self.crouch_pre_press_base
            );
            self.crouch_hold_time_ms = 0;

            if was_hold {
                // Hold: stand up (C held = temporarily crouched, release = stand)
                // This works whether we started standing or were already crouched
                self.base_stance = Stance::Standing;
            } else {
                // Toggle: if was crouching, stand up; otherwise go to crouch
                if self.crouch_pre_press_base == Stance::Crouching {
                    // Was crouching, tapped C -> stand up
                    self.base_stance = Stance::Standing;
                } else {
                    // Was standing or prone, tapped C -> go to crouch
                    self.base_stance = Stance::Crouching;
                }
            }
            log::debug!("crouch released: new base_stance={:?}", self.base_stance);
        }

        // Handle prone key release - determine toggle vs hold based on time
        if prone_just_released && self.prone_active {
            self.prone_active = false;
            let was_hold = self.prone_hold_time_ms >= HOLD_THRESHOLD_MS;
            self.prone_hold_time_ms = 0;

            if was_hold {
                // Hold: revert to the stance before we ever entered prone
                // (hold Z = temporary prone, release should always go back up)
                self.base_stance = self.prone_hold_return_stance;
            } else {
                // Toggle: if was prone, go to crouch; otherwise stay prone
                if self.prone_pre_press_base == Stance::Prone {
                    // Was prone, tapped Z -> go to crouch
                    self.base_stance = Stance::Crouching;
                } else {
                    // Was standing or crouching, tapped Z -> stay prone
                    self.base_stance = Stance::Prone;
                }
            }
        }

        // Calculate effective stance (what we should be at right now)
        let effective_stance = self.calculate_effective_stance();

        // Determine what collision checks we need
        let needs_stand_check = effective_stance.is_higher_than(self.current_stance);
        let needs_crouch_check = effective_stance == Stance::Crouching
            && self.current_stance == Stance::Prone;

        StanceUpdateResult {
            desired_stance: effective_stance,
            needs_stand_check,
            needs_crouch_check,
        }
    }

    /// Apply the actual stance after collision checks.
    pub fn apply_stance(&mut self, stance: Stance) {
        self.current_stance = stance;
    }

    /// Calculate the effective stance based on active keys.
    fn calculate_effective_stance(&self) -> Stance {
        // Priority: Prone (Z active) > Crouch (C active) > base_stance
        if self.prone_active {
            Stance::Prone
        } else if self.crouch_active {
            // Crouch only lowers, doesn't raise
            if self.base_stance == Stance::Prone {
                Stance::Prone // C doesn't raise from prone
            } else {
                Stance::Crouching
            }
        } else {
            self.base_stance
        }
    }

    /// Check if currently crouching.
    pub fn is_crouching(&self) -> bool {
        self.current_stance == Stance::Crouching
    }

    /// Check if currently prone.
    pub fn is_prone(&self) -> bool {
        self.current_stance == Stance::Prone
    }

    /// Check if currently standing.
    pub fn is_standing(&self) -> bool {
        self.current_stance == Stance::Standing
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Simulated frame time (~16ms at 60fps)
    const FRAME_MS: u32 = 16;

    fn no_input() -> StanceInput {
        StanceInput {
            delta_time_ms: FRAME_MS,
            ..Default::default()
        }
    }

    fn crouch_pressed() -> StanceInput {
        StanceInput {
            crouch_pressed: true,
            delta_time_ms: FRAME_MS,
            ..Default::default()
        }
    }

    fn prone_pressed() -> StanceInput {
        StanceInput {
            prone_pressed: true,
            delta_time_ms: FRAME_MS,
            ..Default::default()
        }
    }

    fn stand_requested() -> StanceInput {
        StanceInput {
            stand_requested: true,
            delta_time_ms: FRAME_MS,
            ..Default::default()
        }
    }

    fn both_pressed() -> StanceInput {
        StanceInput {
            crouch_pressed: true,
            prone_pressed: true,
            delta_time_ms: FRAME_MS,
            ..Default::default()
        }
    }

    /// Apply update and immediately apply the desired stance (no collision blocking).
    fn update_and_apply(state: &mut StanceState, input: StanceInput) {
        let result = state.update(input);
        state.apply_stance(result.desired_stance);
    }

    /// Simulate holding a key for given duration then releasing
    fn hold_crouch_for_ms(state: &mut StanceState, hold_ms: u32) {
        // Press
        update_and_apply(state, crouch_pressed());

        // Hold for duration (simulate multiple frames)
        let frames = hold_ms / FRAME_MS;
        for _ in 0..frames {
            update_and_apply(state, crouch_pressed());
        }

        // Release
        update_and_apply(state, no_input());
    }

    fn hold_prone_for_ms(state: &mut StanceState, hold_ms: u32) {
        // Press
        update_and_apply(state, prone_pressed());

        // Hold for duration (simulate multiple frames)
        let frames = hold_ms / FRAME_MS;
        for _ in 0..frames {
            update_and_apply(state, prone_pressed());
        }

        // Release
        update_and_apply(state, no_input());
    }

    // =========================================================================
    // Basic Toggle Tests (tap = press and release quickly < 150ms)
    // =========================================================================

    #[test]
    fn test_01_standing_c_tap_to_crouch() {
        let mut state = StanceState::default();
        assert_eq!(state.current_stance, Stance::Standing);

        // C down - immediately go to crouch, base unchanged yet
        update_and_apply(&mut state, crouch_pressed());
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Standing); // Base changes on release

        // C up (quick release = toggle) - base changes to Crouching
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Crouching);
    }

    #[test]
    fn test_02_crouching_c_tap_to_standing() {
        let mut state = StanceState::new(Stance::Crouching);

        // C down from crouch - current stays crouch (C doesn't raise)
        update_and_apply(&mut state, crouch_pressed());
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Crouching); // Unchanged until release

        // C up (quick = toggle) - base changes to Standing
        update_and_apply(&mut state, no_input());
        assert_eq!(state.base_stance, Stance::Standing);
        assert_eq!(state.current_stance, Stance::Standing);
    }

    #[test]
    fn test_03_standing_z_tap_to_prone() {
        let mut state = StanceState::default();

        // Z down - go to prone
        update_and_apply(&mut state, prone_pressed());
        assert_eq!(state.current_stance, Stance::Prone);
        assert_eq!(state.base_stance, Stance::Standing); // Unchanged until release

        // Z up (quick = toggle) - base changes to Prone
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Prone);
        assert_eq!(state.base_stance, Stance::Prone);
    }

    #[test]
    fn test_04_prone_z_tap_to_crouch() {
        let mut state = StanceState::new(Stance::Prone);

        // Z down from prone - stay prone (Z only goes to prone)
        update_and_apply(&mut state, prone_pressed());
        assert_eq!(state.current_stance, Stance::Prone);

        // Z up (quick = toggle from prone) - base changes to Crouch
        update_and_apply(&mut state, no_input());
        assert_eq!(state.base_stance, Stance::Crouching);
        assert_eq!(state.current_stance, Stance::Crouching);
    }

    #[test]
    fn test_05_crouching_z_tap_to_prone() {
        let mut state = StanceState::new(Stance::Crouching);

        // Z down - go to prone
        update_and_apply(&mut state, prone_pressed());
        assert_eq!(state.current_stance, Stance::Prone);

        // Z up (quick = toggle) - base changes to Prone
        update_and_apply(&mut state, no_input());
        assert_eq!(state.base_stance, Stance::Prone);
        assert_eq!(state.current_stance, Stance::Prone);
    }

    #[test]
    fn test_06_prone_c_tap_to_crouch() {
        let mut state = StanceState::new(Stance::Prone);

        // C down from prone - stay prone (C doesn't raise from prone)
        update_and_apply(&mut state, crouch_pressed());
        assert_eq!(state.current_stance, Stance::Prone);

        // C up (quick = toggle from prone) - base changes to Crouch
        update_and_apply(&mut state, no_input());
        assert_eq!(state.base_stance, Stance::Crouching);
        assert_eq!(state.current_stance, Stance::Crouching);
    }

    // =========================================================================
    // Hold Tests (hold = press and hold > 150ms, then release reverts)
    // =========================================================================

    #[test]
    fn test_07_standing_c_hold_crouch_release_standing() {
        let mut state = StanceState::default();

        // Hold C for > 150ms then release
        hold_crouch_for_ms(&mut state, 200);

        // Should revert to standing (hold behavior)
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    #[test]
    fn test_08_standing_z_hold_prone_release_standing() {
        let mut state = StanceState::default();

        // Hold Z for > 150ms then release
        hold_prone_for_ms(&mut state, 200);

        // Hold Z reverts to pre-press base (Standing)
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    #[test]
    fn test_09_crouching_z_hold_prone_release_crouch() {
        let mut state = StanceState::new(Stance::Crouching);

        // Hold Z for > 150ms then release
        hold_prone_for_ms(&mut state, 200);

        // Hold Z always releases to crouch
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Crouching);
    }

    #[test]
    fn test_10_crouching_c_hold_stands_up() {
        let mut state = StanceState::new(Stance::Crouching);

        // C down from crouch - stays crouched (C doesn't lower from crouch)
        update_and_apply(&mut state, crouch_pressed());
        assert_eq!(state.current_stance, Stance::Crouching);

        // Keep holding C
        for _ in 0..10 {
            update_and_apply(&mut state, crouch_pressed());
        }
        assert_eq!(state.current_stance, Stance::Crouching);

        // C up after hold - stand up (hold C = temporarily crouch, release = stand)
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    // =========================================================================
    // Combined Toggle + Hold Tests
    // =========================================================================

    #[test]
    fn test_11_c_tap_stay_crouched_z_hold_prone_release_back_to_crouch() {
        let mut state = StanceState::default();

        // C tap (toggle to crouch)
        update_and_apply(&mut state, crouch_pressed());
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Crouching);

        // Z hold (goes to prone temporarily)
        hold_prone_for_ms(&mut state, 200);

        // Should revert to crouch (hold behavior)
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Crouching);
    }

    #[test]
    fn test_12_z_tap_stay_prone_c_hold_stands_up() {
        let mut state = StanceState::default();

        // Z tap (toggle to prone)
        update_and_apply(&mut state, prone_pressed());
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Prone);
        assert_eq!(state.base_stance, Stance::Prone);

        // C hold from prone - stays prone while holding (C doesn't lower from prone)
        hold_crouch_for_ms(&mut state, 200);

        // After C release (hold behavior), stand up
        // Hold C always means "temporarily crouch", release = stand
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    #[test]
    fn test_13_prone_z_hold_release_goes_to_standing() {
        // If already prone (from standing), hold Z and release should go to standing
        // because prone_pre_press_base was Standing when we first went prone
        let mut state = StanceState::default(); // Start standing

        // Tap Z to go prone
        update_and_apply(&mut state, prone_pressed());
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Prone);
        assert_eq!(state.base_stance, Stance::Prone);

        // Now hold Z for > 150ms then release
        hold_prone_for_ms(&mut state, 200);

        // Should revert to pre-press base (Standing - from when we first went prone)
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    // =========================================================================
    // Space Key (Jump/Stand) Tests
    // =========================================================================

    #[test]
    fn test_14_crouching_space_to_standing() {
        let mut state = StanceState::new(Stance::Crouching);

        update_and_apply(&mut state, stand_requested());
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    #[test]
    fn test_15_prone_space_to_standing() {
        let mut state = StanceState::new(Stance::Prone);

        update_and_apply(&mut state, stand_requested());
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    #[test]
    fn test_16_holding_z_space_stands_but_returns_to_prone() {
        let mut state = StanceState::default();

        // Z down - go to prone
        update_and_apply(&mut state, prone_pressed());
        assert_eq!(state.current_stance, Stance::Prone);

        // Space while holding Z - stands up temporarily
        let input = StanceInput {
            crouch_pressed: false,
            prone_pressed: true,
            stand_requested: true,
            delta_time_ms: FRAME_MS,
        };
        update_and_apply(&mut state, input);
        assert_eq!(state.current_stance, Stance::Standing);
        // Base unchanged because we're still holding Z
        assert_eq!(state.base_stance, Stance::Standing);

        // Next frame, still holding Z, no stand request - should return to prone
        update_and_apply(&mut state, prone_pressed());
        assert_eq!(state.current_stance, Stance::Prone);
    }

    #[test]
    fn test_17_holding_c_space_stands_but_returns_to_crouch() {
        let mut state = StanceState::default();

        // C down - go to crouch
        update_and_apply(&mut state, crouch_pressed());
        assert_eq!(state.current_stance, Stance::Crouching);

        // Space while holding C - stands up temporarily
        let input = StanceInput {
            crouch_pressed: true,
            prone_pressed: false,
            stand_requested: true,
            delta_time_ms: FRAME_MS,
        };
        update_and_apply(&mut state, input);
        assert_eq!(state.current_stance, Stance::Standing);

        // Next frame, still holding C, no stand request - should return to crouch
        update_and_apply(&mut state, crouch_pressed());
        assert_eq!(state.current_stance, Stance::Crouching);
    }

    // =========================================================================
    // Edge Cases
    // =========================================================================

    #[test]
    fn test_18_both_c_and_z_held_z_takes_priority() {
        let mut state = StanceState::default();

        // Both pressed simultaneously - Z takes priority, we go to prone
        // Base is still Standing (changes on release)
        update_and_apply(&mut state, both_pressed());
        assert_eq!(state.current_stance, Stance::Prone);
        assert_eq!(state.base_stance, Stance::Standing);

        // Keep holding both for a while
        for _ in 0..10 {
            update_and_apply(&mut state, both_pressed());
        }
        assert_eq!(state.current_stance, Stance::Prone);

        // Release Z, still holding C - now just C active, go to crouch
        let input = StanceInput {
            crouch_pressed: true,
            prone_pressed: false,
            stand_requested: false,
            delta_time_ms: FRAME_MS,
        };
        update_and_apply(&mut state, input);
        // Z release was a hold (> 150ms), base reverts to pre-press (Standing)
        // But C is still held, so effective = Crouching
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Standing);

        // Release C (also was a hold)
        update_and_apply(&mut state, no_input());
        // C release was a hold, stand up
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    // =========================================================================
    // User-reported Bug Tests
    // =========================================================================

    #[test]
    fn test_bug_tap_c_wait_tap_c_should_stand() {
        // tap C, wait, tap C --> should go crouch then back to standing
        let mut state = StanceState::default();

        // Tap C (toggle to crouch)
        update_and_apply(&mut state, crouch_pressed());
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Crouching);

        // Wait a few frames
        for _ in 0..10 {
            update_and_apply(&mut state, no_input());
        }
        assert_eq!(state.current_stance, Stance::Crouching);

        // Tap C again (should toggle back to standing)
        update_and_apply(&mut state, crouch_pressed());
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    #[test]
    fn test_bug_hold_c_release_should_stand() {
        // hold C --> should go to crouch, then release should revert to standing
        let mut state = StanceState::default();

        // Hold C for > 150ms then release
        hold_crouch_for_ms(&mut state, 200);

        // Should be back to standing
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    #[test]
    fn test_bug_tap_c_then_hold_c_release_should_stand() {
        // tap C to crouch, then hold C and release -> should stand up
        let mut state = StanceState::default();

        // Tap C (toggle to crouch)
        update_and_apply(&mut state, crouch_pressed());
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Crouching);

        // Now hold C for > 150ms then release
        hold_crouch_for_ms(&mut state, 200);

        // Should stand up (hold C = temporary crouch, release = stand)
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    #[test]
    fn test_bug_tap_z_then_hold_z_release_goes_to_standing() {
        // tap Z to prone, then hold Z and release -> should go back to standing
        // (because we were standing before we first entered prone)
        let mut state = StanceState::default();

        // Tap Z (toggle to prone from standing)
        update_and_apply(&mut state, prone_pressed());
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Prone);
        assert_eq!(state.base_stance, Stance::Prone);

        // Now hold Z for > 150ms then release
        hold_prone_for_ms(&mut state, 200);

        // Should go back to standing (the stance before we first entered prone)
        assert_eq!(state.current_stance, Stance::Standing);
        assert_eq!(state.base_stance, Stance::Standing);
    }

    #[test]
    fn test_bug_tap_c_hold_z_release_smooth_transition() {
        // tap C, wait, hold Z, wait, release Z
        // Should go: standing -> crouch (tap) -> prone (hold) -> crouch (release)
        // WITHOUT going through standing during the prone->crouch transition
        let mut state = StanceState::default();

        // Tap C (toggle to crouch)
        update_and_apply(&mut state, crouch_pressed());
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Crouching);

        // Wait
        for _ in 0..5 {
            update_and_apply(&mut state, no_input());
        }

        // Hold Z - go to prone
        update_and_apply(&mut state, prone_pressed());
        assert_eq!(state.current_stance, Stance::Prone);
        // Base should still be Crouching (Z hold shouldn't change base yet)
        assert_eq!(state.base_stance, Stance::Crouching);

        // Keep holding Z
        for _ in 0..15 {
            update_and_apply(&mut state, prone_pressed());
        }
        assert_eq!(state.current_stance, Stance::Prone);
        assert_eq!(state.base_stance, Stance::Crouching); // Still crouching base

        // Release Z - should go directly to crouch (not through standing)
        update_and_apply(&mut state, no_input());
        assert_eq!(state.current_stance, Stance::Crouching);
        assert_eq!(state.base_stance, Stance::Crouching);
    }

    // =========================================================================
    // Stance Comparison Tests
    // =========================================================================

    #[test]
    fn test_stance_ordering() {
        assert!(Stance::Crouching.is_lower_than(Stance::Standing));
        assert!(Stance::Prone.is_lower_than(Stance::Crouching));
        assert!(Stance::Prone.is_lower_than(Stance::Standing));

        assert!(Stance::Standing.is_higher_than(Stance::Crouching));
        assert!(Stance::Crouching.is_higher_than(Stance::Prone));
        assert!(Stance::Standing.is_higher_than(Stance::Prone));

        assert!(!Stance::Standing.is_lower_than(Stance::Standing));
        assert!(!Stance::Standing.is_higher_than(Stance::Standing));
    }

    #[test]
    fn test_stance_higher_lower() {
        assert_eq!(Stance::Standing.higher(), Stance::Standing);
        assert_eq!(Stance::Crouching.higher(), Stance::Standing);
        assert_eq!(Stance::Prone.higher(), Stance::Crouching);

        assert_eq!(Stance::Standing.lower(), Stance::Crouching);
        assert_eq!(Stance::Crouching.lower(), Stance::Prone);
        assert_eq!(Stance::Prone.lower(), Stance::Prone);
    }
}
