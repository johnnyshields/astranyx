//! Camera configuration for segments.

use glam::Vec3;

/// Camera projection type.
#[derive(Debug, Clone, Copy)]
pub enum CameraProjection {
    /// Perspective projection with field of view.
    Perspective,
    /// Orthographic projection with scale.
    Orthographic {
        /// Orthographic scale (units visible).
        scale: f32,
    },
}

impl Default for CameraProjection {
    fn default() -> Self {
        Self::Perspective
    }
}

impl CameraProjection {
    /// Parse from script string.
    pub fn from_string(s: &str) -> Self {
        match s {
            "orthographic" | "ortho" => Self::Orthographic { scale: 1000.0 },
            _ => Self::Perspective,
        }
    }
}

/// Camera configuration loaded from script.
#[derive(Debug, Clone)]
pub struct CameraConfig {
    /// Projection type.
    pub projection: CameraProjection,

    /// Camera position in world space.
    pub position: Vec3,

    /// Camera target (look-at point).
    pub target: Vec3,

    /// Field of view in degrees (for perspective).
    pub fov: f32,

    /// Near clipping plane.
    pub near: f32,

    /// Far clipping plane.
    pub far: f32,

    /// Whether camera follows the player.
    pub follow_player: bool,

    /// Offset from player when following.
    pub follow_offset: Vec3,

    /// Smoothing factor for camera movement (0 = instant, 1 = very smooth).
    pub smoothing: f32,

    /// Deadzone for player following (player can move this far before camera moves).
    pub deadzone: Vec3,

    /// Whether to allow camera shake effects.
    pub allow_shake: bool,
}

impl Default for CameraConfig {
    fn default() -> Self {
        Self {
            projection: CameraProjection::Perspective,
            position: Vec3::new(960.0, 540.0, 1000.0),
            target: Vec3::new(960.0, 540.0, 0.0),
            fov: 60.0,
            near: 0.1,
            far: 10000.0,
            follow_player: false,
            follow_offset: Vec3::new(0.0, 0.0, 500.0),
            smoothing: 0.0,
            deadzone: Vec3::ZERO,
            allow_shake: true,
        }
    }
}

impl CameraConfig {
    /// Create a config for classic 2D shmup (fixed camera, centered on play area).
    pub fn classic_shmup() -> Self {
        Self {
            projection: CameraProjection::Perspective,
            position: Vec3::new(960.0, 540.0, 1000.0),
            target: Vec3::new(960.0, 540.0, 0.0),
            fov: 60.0,
            follow_player: false,
            ..Default::default()
        }
    }

    /// Create a config for player-following camera.
    pub fn follow_player(offset: Vec3) -> Self {
        Self {
            projection: CameraProjection::Perspective,
            position: Vec3::ZERO, // Will be calculated from player position
            target: Vec3::ZERO,
            fov: 60.0,
            follow_player: true,
            follow_offset: offset,
            smoothing: 0.1,
            ..Default::default()
        }
    }

    /// Create a config for first-person view.
    pub fn first_person() -> Self {
        Self {
            projection: CameraProjection::Perspective,
            position: Vec3::ZERO, // Will be at player position
            target: Vec3::ZERO,   // Will be player forward
            fov: 90.0,
            follow_player: true,
            follow_offset: Vec3::ZERO,
            ..Default::default()
        }
    }

    /// Calculate actual camera position based on player position.
    pub fn calculate_position(&self, player_pos: Vec3, current_pos: Vec3) -> Vec3 {
        if !self.follow_player {
            return self.position;
        }

        let target_pos = player_pos + self.follow_offset;

        if self.smoothing > 0.0 {
            // Lerp towards target
            current_pos.lerp(target_pos, 1.0 - self.smoothing)
        } else {
            target_pos
        }
    }

    /// Calculate camera target based on player position.
    pub fn calculate_target(&self, player_pos: Vec3, player_forward: Vec3) -> Vec3 {
        if !self.follow_player {
            return self.target;
        }

        // For FPS, look in player's forward direction
        // For third person, look at player
        player_pos + player_forward * 100.0
    }
}

/// Runtime camera state.
#[derive(Debug, Clone)]
pub struct CameraState {
    /// Current position (may be interpolating).
    pub position: Vec3,

    /// Current target (may be interpolating).
    pub target: Vec3,

    /// Current shake offset.
    pub shake_offset: Vec3,

    /// Remaining shake frames.
    pub shake_remaining: u32,

    /// Shake intensity.
    pub shake_intensity: f32,
}

impl Default for CameraState {
    fn default() -> Self {
        Self {
            position: Vec3::new(960.0, 540.0, 1000.0),
            target: Vec3::new(960.0, 540.0, 0.0),
            shake_offset: Vec3::ZERO,
            shake_remaining: 0,
            shake_intensity: 0.0,
        }
    }
}

impl CameraState {
    /// Start a camera shake effect.
    pub fn start_shake(&mut self, intensity: f32, duration: u32) {
        self.shake_intensity = intensity;
        self.shake_remaining = duration;
    }

    /// Update camera shake. Returns the shake offset to apply.
    pub fn update_shake(&mut self, rng: &mut crate::random::SeededRandom) -> Vec3 {
        if self.shake_remaining == 0 {
            self.shake_offset = Vec3::ZERO;
            return Vec3::ZERO;
        }

        self.shake_remaining -= 1;

        // Decay intensity over time
        let progress = 1.0 - (self.shake_remaining as f32 / 30.0).min(1.0);
        let intensity = self.shake_intensity * (1.0 - progress);

        // Random offset
        self.shake_offset = Vec3::new(
            (rng.next() - 0.5) * 2.0 * intensity,
            (rng.next() - 0.5) * 2.0 * intensity,
            0.0,
        );

        self.shake_offset
    }

    /// Get the final camera position with shake applied.
    pub fn final_position(&self) -> Vec3 {
        self.position + self.shake_offset
    }
}
