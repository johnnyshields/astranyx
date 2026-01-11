//! Segment types and configuration.
//!
//! A segment is a gameplay section with its own mode, bounds, camera, and spawning.

use bincode::{Decode, Encode};
use glam::Vec3;
use serde::{Deserialize, Serialize};

use crate::physics::WorldBounds3D;
use super::CameraConfig;

/// Game mode determines camera behavior and player controls.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub enum GameMode {
    /// Classic side-scrolling shmup (R-Type, Gradius style).
    /// Fixed camera angle, 2D movement in XY plane.
    SideScroll {
        /// Camera angle in degrees (0 = straight on, 45 = angled).
        angle: f32,
    },

    /// On-rails shmup following a spline path (Starfox style).
    /// Camera follows path, player has limited dodge movement.
    OnRails {
        /// Path ID to follow.
        path_id: String,
    },

    /// Free-flight space combat (Rogue Squadron style).
    /// Full 3D movement with chase camera, turnaround at bounds.
    FreeFlight,

    /// Turret section (on-rails FPS).
    /// Camera follows path, player aims with crosshair.
    Turret {
        /// Path ID to follow.
        path_id: String,
    },

    /// First-person on foot.
    /// Full FPS controls with WASD + mouse.
    FirstPerson,
}

impl Default for GameMode {
    fn default() -> Self {
        Self::SideScroll { angle: 0.0 }
    }
}

impl GameMode {
    /// Parse from script string.
    pub fn from_string(s: &str) -> Self {
        match s {
            "side-scroll" | "sidescroll" => Self::SideScroll { angle: 0.0 },
            "on-rails" | "onrails" | "rails" => Self::OnRails { path_id: String::new() },
            "free-flight" | "freeflight" => Self::FreeFlight,
            "turret" => Self::Turret { path_id: String::new() },
            "first-person" | "firstperson" | "fps" => Self::FirstPerson,
            _ => Self::default(),
        }
    }

    /// Whether this mode uses 2D physics (XY plane only).
    pub fn is_2d(&self) -> bool {
        matches!(self, Self::SideScroll { .. })
    }

    /// Whether this mode is on rails (camera follows a path).
    pub fn is_on_rails(&self) -> bool {
        matches!(self, Self::OnRails { .. } | Self::Turret { .. })
    }

    /// Whether this is a first-person mode.
    pub fn is_first_person(&self) -> bool {
        matches!(self, Self::FirstPerson | Self::Turret { .. })
    }

    /// Whether this allows full 3D movement.
    pub fn is_3d_free(&self) -> bool {
        matches!(self, Self::FreeFlight | Self::FirstPerson)
    }
}

/// Segment configuration loaded from script.
#[derive(Debug, Clone)]
pub struct SegmentConfig {
    /// Unique segment ID.
    pub id: String,

    /// Display name.
    pub name: String,

    /// Game mode for this segment.
    pub mode: GameMode,

    /// World bounds for the play area.
    pub bounds: WorldBounds3D,

    /// Camera configuration.
    pub camera: CameraConfig,

    /// Background layers for parallax scrolling.
    pub backgrounds: Vec<BackgroundLayer>,

    /// Segment duration in frames (None = infinite/triggered).
    pub duration: Option<u32>,

    /// Scroll configuration.
    pub scroll: Option<ScrollConfig>,

    /// Available enemy types for spawning.
    pub wave_pool: Vec<String>,

    /// Base spawn rate (waves per second).
    pub spawn_rate: f32,

    /// Difficulty curve type.
    pub difficulty_curve: DifficityCurve,

    /// Placeholder geometry for level visuals.
    pub geometry: Vec<GeometryDef>,

    /// Light sources for the segment.
    pub lights: Vec<LightDef>,

    /// Player starting position for this segment.
    pub player_start: Option<Vec3>,
}

impl SegmentConfig {
    /// Get all solid geometry for collision detection.
    pub fn solid_geometry(&self) -> impl Iterator<Item = &GeometryDef> {
        self.geometry.iter().filter(|g| g.solid)
    }
}

/// A placeholder geometry definition.
#[derive(Debug, Clone)]
pub struct GeometryDef {
    /// Geometry type (box, cylinder, etc).
    pub geo_type: String,
    /// Position in world space.
    pub position: Vec3,
    /// Size (width, height, depth for box).
    pub size: Vec3,
    /// Color (RGB, 0-255).
    pub color: [u8; 3],
    /// Whether this geometry blocks player movement.
    pub solid: bool,
    /// Optional tag for scripting (e.g., "door", "cover", "light").
    pub tag: Option<String>,
}

/// Light source definition for FPS levels.
#[derive(Debug, Clone)]
pub struct LightDef {
    /// Light type (point, spot, directional).
    pub light_type: LightType,
    /// Position in world space.
    pub position: Vec3,
    /// Light color (RGB, 0-255).
    pub color: [u8; 3],
    /// Light intensity (0.0-10.0).
    pub intensity: f32,
    /// Range for point/spot lights.
    pub range: f32,
    /// Spot angle in degrees (for spot lights).
    pub spot_angle: Option<f32>,
    /// Direction for spot/directional lights.
    pub direction: Option<Vec3>,
}

/// Light types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LightType {
    Point,
    Spot,
    Directional,
}

impl LightType {
    pub fn from_string(s: &str) -> Self {
        match s {
            "point" => Self::Point,
            "spot" => Self::Spot,
            "directional" | "dir" => Self::Directional,
            _ => Self::Point,
        }
    }
}

impl Default for LightDef {
    fn default() -> Self {
        Self {
            light_type: LightType::Point,
            position: Vec3::ZERO,
            color: [255, 255, 255],
            intensity: 1.0,
            range: 100.0,
            spot_angle: None,
            direction: None,
        }
    }
}

impl Default for SegmentConfig {
    fn default() -> Self {
        Self {
            id: String::new(),
            name: String::new(),
            mode: GameMode::default(),
            bounds: WorldBounds3D::default(),
            camera: CameraConfig::default(),
            backgrounds: Vec::new(),
            duration: None,
            scroll: Some(ScrollConfig::default()),
            wave_pool: vec!["grunt".to_string()],
            spawn_rate: 1.0,
            difficulty_curve: DifficityCurve::Linear,
            geometry: Vec::new(),
            lights: Vec::new(),
            player_start: None,
        }
    }
}

/// Background layer for parallax scrolling.
#[derive(Debug, Clone)]
pub struct BackgroundLayer {
    /// Layer asset name.
    pub layer: String,

    /// Scroll speed multiplier (0.0 = static, 1.0 = matches camera).
    pub scroll_speed: f32,

    /// Z position for depth sorting.
    pub z: f32,
}

/// Scroll configuration for auto-scrolling segments.
#[derive(Debug, Clone)]
pub struct ScrollConfig {
    /// Whether scrolling is enabled.
    pub enabled: bool,

    /// Scroll direction (normalized).
    pub direction: Vec3,

    /// Scroll speed in world units per second.
    pub speed: f32,
}

impl Default for ScrollConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            direction: Vec3::new(1.0, 0.0, 0.0), // Scroll right
            speed: 60.0,
        }
    }
}

/// Difficulty curve types for spawn rate scaling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DifficityCurve {
    /// Linear increase.
    Linear,
    /// Exponential increase.
    Exponential,
    /// Stepped (difficulty tiers).
    Stepped,
    /// Flat (no scaling).
    Flat,
}

impl DifficityCurve {
    /// Parse from script string.
    pub fn from_string(s: &str) -> Self {
        match s {
            "linear" => Self::Linear,
            "exponential" => Self::Exponential,
            "stepped" => Self::Stepped,
            "flat" | "none" => Self::Flat,
            _ => Self::Linear,
        }
    }

    /// Calculate difficulty multiplier for the given segment frame.
    pub fn multiplier(&self, frame: u32, _base_rate: f32) -> f32 {
        let t = frame as f32 / 1800.0; // Normalize to ~60 seconds
        match self {
            Self::Linear => 1.0 + t * 0.5,
            Self::Exponential => (1.0 + t).powf(1.5),
            Self::Stepped => {
                let tier = (frame / 600) as f32; // Every 20 seconds
                1.0 + tier * 0.3
            }
            Self::Flat => 1.0,
        }
    }
}
