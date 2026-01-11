//! Alert state machine for enemy AI.
//!
//! MGS-style alert progression:
//! - Unaware: Normal patrol behavior
//! - Curious: Heard something, investigating
//! - Alert: Spotted something suspicious
//! - Evasion: Player seen, triggering alarm
//! - Combat: Actively engaging player
//! - Search: Lost sight, searching last known position
//!
//! Alert levels affect enemy behavior, movement speed, and accuracy.

use glam::Vec3;

/// Alert level enum matching MGS progression.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AlertLevel {
    /// Normal patrol/idle behavior
    #[default]
    Unaware,
    /// Heard a sound, moving to investigate
    Curious,
    /// Saw something suspicious (peripheral vision)
    Alert,
    /// Confirmed player sighting, raising alarm
    Evasion,
    /// Actively engaging in combat
    Combat,
    /// Lost target, searching last known position
    Search,
}

impl AlertLevel {
    /// Get the icon/indicator for this alert level (for HUD display).
    pub fn indicator(&self) -> &'static str {
        match self {
            AlertLevel::Unaware => "",
            AlertLevel::Curious => "?",
            AlertLevel::Alert => "!?",
            AlertLevel::Evasion => "!!",
            AlertLevel::Combat => "!!!",
            AlertLevel::Search => "...",
        }
    }

    /// Get movement speed multiplier for this alert level.
    pub fn speed_multiplier(&self) -> f32 {
        match self {
            AlertLevel::Unaware => 0.5,  // Slow patrol
            AlertLevel::Curious => 0.7,  // Walking to check
            AlertLevel::Alert => 0.8,    // Moving cautiously
            AlertLevel::Evasion => 1.2,  // Running to alarm
            AlertLevel::Combat => 1.0,   // Combat movement
            AlertLevel::Search => 0.6,   // Searching carefully
        }
    }

    /// Get accuracy multiplier for this alert level.
    pub fn accuracy_multiplier(&self) -> f32 {
        match self {
            AlertLevel::Unaware => 0.3,  // Not expecting combat
            AlertLevel::Curious => 0.4,
            AlertLevel::Alert => 0.6,
            AlertLevel::Evasion => 0.7,
            AlertLevel::Combat => 1.0,   // Full combat readiness
            AlertLevel::Search => 0.8,
        }
    }

    /// Whether this level should trigger the global alert.
    pub fn triggers_global_alert(&self) -> bool {
        matches!(self, AlertLevel::Evasion | AlertLevel::Combat)
    }

    /// Whether enemies can be distracted at this level.
    pub fn can_be_distracted(&self) -> bool {
        matches!(
            self,
            AlertLevel::Unaware | AlertLevel::Curious | AlertLevel::Search
        )
    }
}

/// Full alert state with timers and context.
#[derive(Debug, Clone, Default)]
pub struct AlertState {
    /// Current alert level
    pub level: AlertLevel,
    /// Frames in current state
    pub state_frames: u32,
    /// Investigation target position (for Curious/Search)
    pub investigate_pos: Option<Vec3>,
    /// Confirmed player position (for Combat)
    pub target_pos: Option<Vec3>,
    /// Suspicion accumulator (0.0-1.0, triggers Alert at threshold)
    pub suspicion: f32,
    /// Frames since last seeing player (for Search timeout)
    pub frames_since_sight: u32,
}

impl AlertState {
    /// Suspicion threshold to transition from Curious to Alert
    pub const SUSPICION_THRESHOLD: f32 = 0.8;
    /// Frames in Curious before giving up
    pub const CURIOUS_TIMEOUT: u32 = 180; // 6 seconds at 30fps
    /// Frames in Search before returning to Unaware
    pub const SEARCH_TIMEOUT: u32 = 300; // 10 seconds
    /// Frames in Alert before calming down (if no further sighting)
    pub const ALERT_TIMEOUT: u32 = 240; // 8 seconds

    pub fn new() -> Self {
        Self::default()
    }

    /// Transition to a new alert level.
    pub fn transition_to(&mut self, level: AlertLevel) {
        if self.level != level {
            self.level = level;
            self.state_frames = 0;

            // Reset context based on new level
            match level {
                AlertLevel::Unaware => {
                    self.investigate_pos = None;
                    self.target_pos = None;
                    self.suspicion = 0.0;
                }
                AlertLevel::Search => {
                    // Keep target_pos as last known position
                    self.investigate_pos = self.target_pos;
                }
                _ => {}
            }
        }
    }

    /// Update the state machine for one frame.
    /// Returns true if alert level changed.
    pub fn update(&mut self) -> bool {
        self.state_frames += 1;
        let old_level = self.level;

        match self.level {
            AlertLevel::Curious => {
                if self.state_frames >= Self::CURIOUS_TIMEOUT && self.suspicion < 0.3 {
                    self.transition_to(AlertLevel::Unaware);
                }
            }
            AlertLevel::Alert => {
                if self.state_frames >= Self::ALERT_TIMEOUT && self.suspicion < 0.5 {
                    self.transition_to(AlertLevel::Curious);
                }
            }
            AlertLevel::Search => {
                self.frames_since_sight += 1;
                if self.frames_since_sight >= Self::SEARCH_TIMEOUT {
                    self.transition_to(AlertLevel::Unaware);
                }
            }
            AlertLevel::Combat => {
                self.frames_since_sight += 1;
                // Lost sight of player - go to search
                if self.frames_since_sight >= 90 {
                    // 3 seconds
                    self.transition_to(AlertLevel::Search);
                }
            }
            _ => {}
        }

        // Decay suspicion over time (slowly)
        if self.level != AlertLevel::Combat && self.level != AlertLevel::Evasion {
            self.suspicion = (self.suspicion - 0.001).max(0.0);
        }

        old_level != self.level
    }

    /// Called when enemy hears a sound.
    /// Returns true if this should trigger investigation.
    pub fn on_hear_sound(&mut self, sound_pos: Vec3, sound_loudness: f32) -> bool {
        let suspicion_gain = sound_loudness * 0.3;
        self.suspicion = (self.suspicion + suspicion_gain).min(1.0);

        match self.level {
            AlertLevel::Unaware => {
                if sound_loudness > 0.5 {
                    self.investigate_pos = Some(sound_pos);
                    self.transition_to(AlertLevel::Curious);
                    return true;
                }
            }
            AlertLevel::Curious | AlertLevel::Search => {
                // Update investigation position to new sound
                self.investigate_pos = Some(sound_pos);
                return true;
            }
            _ => {}
        }

        false
    }

    /// Called when enemy sees player in peripheral vision.
    pub fn on_peripheral_sight(&mut self, player_pos: Vec3) {
        self.suspicion = (self.suspicion + 0.1).min(1.0);
        self.frames_since_sight = 0;

        match self.level {
            AlertLevel::Unaware => {
                self.investigate_pos = Some(player_pos);
                self.transition_to(AlertLevel::Curious);
            }
            AlertLevel::Curious => {
                self.investigate_pos = Some(player_pos);
                if self.suspicion >= Self::SUSPICION_THRESHOLD {
                    self.transition_to(AlertLevel::Alert);
                }
            }
            AlertLevel::Search => {
                self.investigate_pos = Some(player_pos);
                self.transition_to(AlertLevel::Alert);
            }
            _ => {}
        }
    }

    /// Called when enemy has clear sight of player.
    pub fn on_full_sight(&mut self, player_pos: Vec3) {
        self.suspicion = 1.0;
        self.frames_since_sight = 0;
        self.target_pos = Some(player_pos);

        match self.level {
            AlertLevel::Unaware | AlertLevel::Curious | AlertLevel::Alert => {
                self.transition_to(AlertLevel::Evasion);
            }
            AlertLevel::Search => {
                self.transition_to(AlertLevel::Combat);
            }
            AlertLevel::Evasion => {
                // After evasion period, go to combat
                if self.state_frames >= 60 {
                    self.transition_to(AlertLevel::Combat);
                }
            }
            AlertLevel::Combat => {
                // Already in combat, just update position
            }
        }
    }

    /// Called when enemy reaches investigation position and finds nothing.
    pub fn on_investigation_complete(&mut self) {
        match self.level {
            AlertLevel::Curious => {
                self.suspicion = (self.suspicion - 0.3).max(0.0);
                if self.suspicion < 0.3 {
                    self.transition_to(AlertLevel::Unaware);
                }
            }
            AlertLevel::Search => {
                self.suspicion = (self.suspicion - 0.2).max(0.0);
                // Continue searching
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alert_progression() {
        let mut state = AlertState::new();
        assert_eq!(state.level, AlertLevel::Unaware);

        // Hear a loud sound
        state.on_hear_sound(Vec3::new(10.0, 0.0, 0.0), 0.8);
        assert_eq!(state.level, AlertLevel::Curious);

        // See player in peripheral
        state.on_peripheral_sight(Vec3::new(15.0, 0.0, 0.0));
        // Still curious, building suspicion
        assert_eq!(state.level, AlertLevel::Curious);

        // More peripheral sightings
        for _ in 0..10 {
            state.on_peripheral_sight(Vec3::new(15.0, 0.0, 0.0));
        }
        assert_eq!(state.level, AlertLevel::Alert);

        // Full sight
        state.on_full_sight(Vec3::new(20.0, 0.0, 0.0));
        assert_eq!(state.level, AlertLevel::Evasion);
    }

    #[test]
    fn test_timeout_cooldown() {
        let mut state = AlertState::new();
        state.transition_to(AlertLevel::Curious);

        // Run through timeout
        for _ in 0..AlertState::CURIOUS_TIMEOUT + 10 {
            state.update();
        }

        assert_eq!(state.level, AlertLevel::Unaware);
    }

    #[test]
    fn test_combat_to_search() {
        let mut state = AlertState::new();
        state.on_full_sight(Vec3::new(10.0, 0.0, 0.0));
        state.transition_to(AlertLevel::Combat);

        // Run frames without seeing player
        for _ in 0..100 {
            state.update();
        }

        assert_eq!(state.level, AlertLevel::Search);
    }
}
