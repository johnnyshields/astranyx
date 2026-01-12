//! Movement configuration constants.
//!
//! All movement parameters are grouped here for easy tuning.
//! Based on Quake 3 / Daemon values but adjusted for metric units.

use serde::{Deserialize, Serialize};

/// Configuration for player movement physics.
///
/// All values use metric units (meters, seconds) unless otherwise noted.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MovementConfig {
    // ========================================================================
    // Player Dimensions
    // ========================================================================
    /// Collision radius (meters).
    pub player_radius: f32,

    /// Standing height (meters).
    pub standing_height: f32,

    /// Crouching height (meters).
    pub crouching_height: f32,

    /// Prone height (meters).
    pub prone_height: f32,

    /// Eye height when standing (meters from feet).
    pub eye_height_standing: f32,

    /// Eye height when crouching (meters from feet).
    pub eye_height_crouching: f32,

    /// Eye height when prone (meters from ground).
    pub eye_height_prone: f32,

    // ========================================================================
    // Movement Speeds
    // ========================================================================
    /// Walking speed (meters/second).
    pub walk_speed: f32,

    /// Running/sprinting speed (meters/second).
    pub run_speed: f32,

    /// Crouching speed (meters/second).
    pub crouch_speed: f32,

    /// Prone crawling speed (meters/second).
    pub prone_speed: f32,

    /// Swimming speed (meters/second).
    pub swim_speed: f32,

    // ========================================================================
    // Physics
    // ========================================================================
    /// Gravity acceleration (meters/second²).
    pub gravity: f32,

    /// Jump velocity (meters/second).
    pub jump_velocity: f32,

    /// Ground friction coefficient.
    pub friction: f32,

    /// Air control factor (0.0 = no air control, 1.0 = full control).
    pub air_control: f32,

    /// Ground acceleration (units/second²).
    pub ground_acceleration: f32,

    /// Air acceleration (units/second²).
    pub air_acceleration: f32,

    /// Speed below which player stops completely (meters/second).
    pub stop_speed: f32,

    // ========================================================================
    // Stairs and Steps
    // ========================================================================
    /// Maximum step height player can climb (meters).
    pub step_height: f32,

    /// Minimum surface normal Y to be considered ground (cos of max slope angle).
    /// 0.7 ≈ 45 degrees, 0.85 ≈ 32 degrees
    pub min_ground_normal: f32,

    // ========================================================================
    // Collision
    // ========================================================================
    /// Maximum collision iterations per frame.
    pub max_clip_planes: usize,

    /// Small distance to back off from surfaces (meters).
    pub surface_epsilon: f32,

    /// Overbounce factor for velocity reflection (prevents sticking).
    pub overbounce: f32,

    // ========================================================================
    // Timers (milliseconds)
    // ========================================================================
    /// Minimum time between jumps.
    pub jump_cooldown_ms: u32,

    /// Time to transition from standing to crouching.
    pub crouch_time_ms: u32,

    /// Time to transition to/from prone.
    pub prone_time_ms: u32,
}

impl Default for MovementConfig {
    fn default() -> Self {
        Self {
            // Player dimensions
            player_radius: 0.4,
            standing_height: 1.8,
            crouching_height: 1.0,
            prone_height: 0.4,
            eye_height_standing: 1.6,
            eye_height_crouching: 0.75,
            eye_height_prone: 0.25,

            // Movement speeds (realistic-ish for tactical shooter)
            walk_speed: 4.5,      // ~16 km/h walking
            run_speed: 7.0,       // ~25 km/h sprinting
            crouch_speed: 2.0,    // ~7 km/h sneaking
            prone_speed: 0.8,     // ~3 km/h crawling
            swim_speed: 3.0,      // Swimming

            // Physics
            gravity: 15.0,        // Slightly lower than real (9.8) for game feel
            jump_velocity: 5.5,   // Gives ~1m jump height
            friction: 6.0,        // Ground friction
            air_control: 0.1,     // Very limited air control
            ground_acceleration: 10.0,
            air_acceleration: 1.0,
            stop_speed: 0.5,

            // Steps
            step_height: 0.4,     // 40cm steps (standard stair height)
            min_ground_normal: 0.7, // ~45 degree max slope

            // Collision
            max_clip_planes: 5,
            surface_epsilon: 0.01,
            overbounce: 1.001,

            // Timers
            jump_cooldown_ms: 200,
            crouch_time_ms: 150,
            prone_time_ms: 300,
        }
    }
}

impl MovementConfig {
    /// Create a "fast arcade" movement config (Quake-like).
    pub fn arcade() -> Self {
        Self {
            walk_speed: 6.0,
            run_speed: 10.0,
            crouch_speed: 3.0,
            gravity: 20.0,
            jump_velocity: 6.5,
            friction: 6.0,
            air_control: 0.3,    // More air control for strafing
            ground_acceleration: 15.0,
            air_acceleration: 2.0,
            jump_cooldown_ms: 100,
            ..Default::default()
        }
    }

    /// Create a "tactical" movement config (slower, more realistic).
    pub fn tactical() -> Self {
        Self {
            walk_speed: 3.5,
            run_speed: 5.5,
            crouch_speed: 1.5,
            prone_speed: 0.5,
            gravity: 12.0,
            jump_velocity: 4.5,
            friction: 8.0,
            air_control: 0.05,   // Minimal air control
            ground_acceleration: 8.0,
            air_acceleration: 0.5,
            jump_cooldown_ms: 300,
            prone_time_ms: 400,
            ..Default::default()
        }
    }

    /// Get the max speed for the current movement mode.
    pub fn max_speed(&self, is_crouching: bool, is_sprinting: bool, is_prone: bool) -> f32 {
        if is_prone {
            self.prone_speed
        } else if is_crouching {
            self.crouch_speed
        } else if is_sprinting {
            self.run_speed
        } else {
            self.walk_speed
        }
    }

    /// Get player height for the current stance.
    pub fn height(&self, is_crouching: bool, is_prone: bool) -> f32 {
        if is_prone {
            self.prone_height
        } else if is_crouching {
            self.crouching_height
        } else {
            self.standing_height
        }
    }

    /// Get eye height for the current stance.
    pub fn eye_height(&self, is_crouching: bool, is_prone: bool) -> f32 {
        if is_prone {
            self.eye_height_prone
        } else if is_crouching {
            self.eye_height_crouching
        } else {
            self.eye_height_standing
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = MovementConfig::default();
        assert!(config.walk_speed > 0.0);
        assert!(config.gravity > 0.0);
        assert!(config.player_radius > 0.0);
    }

    #[test]
    fn test_max_speed() {
        let config = MovementConfig::default();

        assert_eq!(config.max_speed(false, false, true), config.prone_speed);
        assert_eq!(config.max_speed(true, false, false), config.crouch_speed);
        assert_eq!(config.max_speed(false, true, false), config.run_speed);
        assert_eq!(config.max_speed(false, false, false), config.walk_speed);
        // Prone overrides everything
        assert_eq!(config.max_speed(true, true, true), config.prone_speed);
        // Crouching overrides sprinting
        assert_eq!(config.max_speed(true, true, false), config.crouch_speed);
    }
}
