//! Player stealth mechanics.
//!
//! MGS-style stealth actions:
//! - Crouch: Reduces visibility and footstep noise
//! - Prone: Maximum stealth, very slow movement
//! - Cover: Press against walls, peek around corners
//! - Takedowns: Silent melee from behind
//!
//! The stealth state affects visibility calculations and sound generation.

use crate::entities::Player;

/// Player's current stealth posture.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Posture {
    /// Normal standing
    #[default]
    Standing,
    /// Crouched (Ctrl held)
    Crouching,
    /// Prone on ground (Z key)
    Prone,
}

impl Posture {
    /// Movement speed multiplier for this posture.
    pub fn speed_multiplier(&self) -> f32 {
        match self {
            Posture::Standing => 1.0,
            Posture::Crouching => 0.5,
            Posture::Prone => 0.2,
        }
    }

    /// Visibility multiplier (how easy to spot).
    pub fn visibility_multiplier(&self) -> f32 {
        match self {
            Posture::Standing => 1.0,
            Posture::Crouching => 0.6,
            Posture::Prone => 0.3,
        }
    }

    /// Sound generation multiplier for footsteps.
    pub fn sound_multiplier(&self) -> f32 {
        match self {
            Posture::Standing => 1.0,
            Posture::Crouching => 0.3,
            Posture::Prone => 0.1,
        }
    }

    /// Height offset for camera/hitbox.
    pub fn height(&self) -> f32 {
        match self {
            Posture::Standing => 1.7,
            Posture::Crouching => 1.0,
            Posture::Prone => 0.3,
        }
    }

    /// Hitbox radius multiplier.
    pub fn hitbox_multiplier(&self) -> f32 {
        match self {
            Posture::Standing => 1.0,
            Posture::Crouching => 0.8,
            Posture::Prone => 0.5,
        }
    }
}

/// Cover state when near walls.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CoverState {
    /// Not in cover
    #[default]
    None,
    /// Pressed against wall (left side)
    WallLeft,
    /// Pressed against wall (right side)
    WallRight,
    /// Behind low cover
    LowCover,
    /// Peeking from cover (temporarily exposed)
    Peeking,
}

impl CoverState {
    pub fn is_in_cover(&self) -> bool {
        !matches!(self, CoverState::None | CoverState::Peeking)
    }

    /// Visibility multiplier when in this cover state.
    pub fn visibility_multiplier(&self) -> f32 {
        match self {
            CoverState::None => 1.0,
            CoverState::WallLeft | CoverState::WallRight => 0.3,
            CoverState::LowCover => 0.2,
            CoverState::Peeking => 0.7,
        }
    }
}

/// Complete stealth state for a player.
#[derive(Debug, Clone, Default)]
pub struct StealthState {
    /// Current posture
    pub posture: Posture,
    /// Current cover state
    pub cover: CoverState,
    /// Whether currently moving
    pub is_moving: bool,
    /// Whether currently running (shift held)
    pub is_running: bool,
    /// Light level at current position (0.0-1.0)
    pub light_level: f32,
    /// Frames in current posture (for transition animations)
    pub posture_frames: u32,
}

impl StealthState {
    pub fn new() -> Self {
        Self {
            light_level: 1.0, // Default to bright
            ..Default::default()
        }
    }

    /// Calculate overall visibility score (for vision system).
    /// Lower = harder to see.
    pub fn visibility(&self) -> f32 {
        let mut vis = 1.0;

        // Posture
        vis *= self.posture.visibility_multiplier();

        // Cover
        vis *= self.cover.visibility_multiplier();

        // Movement
        if self.is_running {
            vis *= 1.5; // Much more visible when running
        } else if self.is_moving {
            vis *= 1.2;
        }

        // Light level
        vis *= self.light_level.clamp(0.1, 1.0);

        vis.clamp(0.05, 2.0)
    }

    /// Calculate sound generation multiplier (for sound system).
    pub fn sound_level(&self) -> f32 {
        let mut sound = 1.0;

        // Posture
        sound *= self.posture.sound_multiplier();

        // Running is louder
        if self.is_running {
            sound *= 2.0;
        } else if !self.is_moving {
            sound *= 0.0; // Silent when still
        }

        sound.clamp(0.0, 3.0)
    }

    /// Get movement speed multiplier.
    pub fn speed_multiplier(&self) -> f32 {
        let base = self.posture.speed_multiplier();
        if self.is_running && self.posture == Posture::Standing {
            base * 1.8 // Sprint speed
        } else {
            base
        }
    }

    /// Update stealth state from player data.
    pub fn from_player(player: &Player) -> Self {
        // Determine posture from player flags
        // TODO: Add crouch/prone flags to Player struct
        Self {
            posture: Posture::Standing,
            cover: CoverState::None,
            is_moving: player.velocity_3d.length_squared() > 0.1,
            is_running: false,
            light_level: 1.0,
            posture_frames: 0,
        }
    }

    /// Transition to a new posture (with frame tracking).
    pub fn set_posture(&mut self, posture: Posture) {
        if self.posture != posture {
            self.posture = posture;
            self.posture_frames = 0;
        } else {
            self.posture_frames += 1;
        }
    }

    /// Check if we can perform a stealth takedown.
    /// Requires: behind enemy, enemy unaware, not running.
    pub fn can_takedown(&self) -> bool {
        !self.is_running && (self.posture == Posture::Crouching || self.posture == Posture::Standing)
    }
}

/// Detection meter that fills up as player is spotted.
/// Similar to MGS's "!" detection.
#[derive(Debug, Clone, Default)]
pub struct DetectionMeter {
    /// Current fill (0.0-1.0)
    pub fill: f32,
    /// Rate at which meter fills when spotted
    pub fill_rate: f32,
    /// Rate at which meter drains when hidden
    pub drain_rate: f32,
    /// Threshold for full detection (triggers combat)
    pub threshold: f32,
}

impl DetectionMeter {
    pub fn new() -> Self {
        Self {
            fill: 0.0,
            fill_rate: 0.05,  // ~20 frames to fill at constant visibility
            drain_rate: 0.02, // ~50 frames to drain
            threshold: 1.0,
        }
    }

    /// Update the meter based on visibility.
    /// Returns true if threshold was crossed (detected!).
    pub fn update(&mut self, visibility: f32, is_being_seen: bool) -> bool {
        let old_fill = self.fill;

        if is_being_seen {
            self.fill += self.fill_rate * visibility;
        } else {
            self.fill -= self.drain_rate;
        }

        self.fill = self.fill.clamp(0.0, self.threshold);

        // Return true if we just crossed the threshold
        old_fill < self.threshold && self.fill >= self.threshold
    }

    /// Reset the meter (e.g., after escaping detection).
    pub fn reset(&mut self) {
        self.fill = 0.0;
    }

    /// Get fill percentage (0.0-1.0).
    pub fn percentage(&self) -> f32 {
        self.fill / self.threshold
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_visibility_calculation() {
        let mut state = StealthState::new();

        // Standing, bright, still
        state.is_moving = false;
        let vis1 = state.visibility();

        // Crouching, bright, still
        state.posture = Posture::Crouching;
        let vis2 = state.visibility();
        assert!(vis2 < vis1);

        // Crouching, dark, still
        state.light_level = 0.2;
        let vis3 = state.visibility();
        assert!(vis3 < vis2);

        // Prone in cover
        state.posture = Posture::Prone;
        state.cover = CoverState::LowCover;
        let vis4 = state.visibility();
        assert!(vis4 < vis3);
    }

    #[test]
    fn test_detection_meter() {
        let mut meter = DetectionMeter::new();

        // Fill while visible
        for _ in 0..15 {
            let detected = meter.update(1.0, true);
            if detected {
                break;
            }
        }

        assert!(meter.fill > 0.5);

        // Drain while hidden
        for _ in 0..30 {
            meter.update(0.0, false);
        }

        assert!(meter.fill < 0.5);
    }
}
