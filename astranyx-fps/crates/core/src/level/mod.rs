//! Level system for Astranyx.
//!
//! Organizes the game into Worlds (stages), Segments (gameplay sections),
//! and Routes (connections with triggers).

pub mod camera;
pub mod mesh;
pub mod route;
pub mod segment;
pub mod test_level;

use bincode::{Decode, Encode};
use glam::Vec3;
use serde::{Deserialize, Serialize};

use crate::physics::WorldBounds3D;

pub use camera::{CameraConfig, CameraProjection, CameraState};
pub use route::{Route, RouteTrigger, Transition, TransitionType};
pub use mesh::{CollisionShape, CollisionWorld, LevelLight, LevelLightType, LevelMesh, MeshTransform, RenderMesh};
pub use segment::{BackgroundLayer, GameMode, GeometryDef, LightDef, LightType, ScrollConfig, SegmentConfig};
pub use test_level::{generate_test_arena, generate_minimal_test};

/// World definition loaded from script.
#[derive(Debug, Clone)]
pub struct WorldDef {
    pub id: String,
    pub name: String,
    pub description: String,
    pub start_segment: String,
    pub music: String,
    pub skybox: String,
}

/// Runtime state for the current level.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct LevelState {
    /// Current world ID.
    pub world_id: String,

    /// Current segment ID.
    pub segment_id: String,

    /// Frame counter within the current segment.
    pub segment_frame: u32,

    /// Scroll offset (3D for flexibility).
    #[bincode(with_serde)]
    pub scroll_offset: Vec3,

    /// Current game mode.
    pub mode: GameMode,

    /// Current world bounds.
    #[bincode(with_serde)]
    pub bounds: WorldBounds3D,

    /// Enemies killed in this segment.
    pub enemies_killed: u32,

    /// Total enemies spawned in this segment.
    pub enemies_spawned: u32,

    /// Whether the boss has been defeated.
    pub boss_defeated: bool,

    /// Secrets found in this segment.
    pub secrets_found: u32,

    /// Damage taken in this segment.
    pub damage_taken: u32,

    /// Pending player choice (for branching routes).
    pub pending_choice: Option<PendingChoice>,

    /// Current cutscene state.
    pub cutscene: Option<CutsceneState>,

    /// Transition state (when moving between segments).
    pub transition: Option<TransitionState>,
}

impl Default for LevelState {
    fn default() -> Self {
        Self {
            world_id: String::new(),
            segment_id: String::new(),
            segment_frame: 0,
            scroll_offset: Vec3::ZERO,
            mode: GameMode::SideScroll { angle: 0.0 },
            bounds: WorldBounds3D::default(),
            enemies_killed: 0,
            enemies_spawned: 0,
            boss_defeated: false,
            secrets_found: 0,
            damage_taken: 0,
            pending_choice: None,
            cutscene: None,
            transition: None,
        }
    }
}

impl LevelState {
    /// Create a new level state for the given world and segment.
    pub fn new(world_id: &str, segment_id: &str) -> Self {
        Self {
            world_id: world_id.to_string(),
            segment_id: segment_id.to_string(),
            ..Default::default()
        }
    }

    /// Reset segment-specific counters (called on segment transition).
    pub fn reset_segment_stats(&mut self) {
        self.segment_frame = 0;
        self.enemies_killed = 0;
        self.enemies_spawned = 0;
        self.boss_defeated = false;
        self.secrets_found = 0;
        self.damage_taken = 0;
    }

    /// Start a transition to a new segment.
    pub fn start_transition(&mut self, to_segment: &str, transition_type: TransitionType, duration: u32) {
        self.transition = Some(TransitionState {
            from_segment: self.segment_id.clone(),
            to_segment: to_segment.to_string(),
            transition_type,
            duration,
            elapsed: 0,
        });
    }

    /// Update transition state. Returns true if transition completed.
    pub fn update_transition(&mut self) -> bool {
        if let Some(ref mut t) = self.transition {
            t.elapsed += 1;
            if t.elapsed >= t.duration {
                // Transition complete - switch to new segment
                self.segment_id = t.to_segment.clone();
                self.reset_segment_stats();
                self.transition = None;
                return true;
            }
        }
        false
    }

    /// Get transition progress as 0.0 to 1.0.
    pub fn transition_progress(&self) -> f32 {
        self.transition.as_ref().map(|t| {
            if t.duration == 0 {
                1.0
            } else {
                t.elapsed as f32 / t.duration as f32
            }
        }).unwrap_or(0.0)
    }
}

/// Pending player choice for branching routes.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct PendingChoice {
    /// Available choices (segment IDs).
    pub options: Vec<String>,

    /// Prompt text to display.
    pub prompt: String,

    /// Frames remaining before timeout.
    pub timeout_remaining: u32,

    /// Default choice index on timeout.
    pub default_index: usize,

    /// Votes from each player (index into options, or None if not voted).
    pub player_votes: Vec<Option<usize>>,
}

impl PendingChoice {
    /// Check if all players have voted.
    pub fn all_voted(&self, player_count: usize) -> bool {
        self.player_votes.iter().take(player_count).all(|v| v.is_some())
    }

    /// Get the winning choice index (majority, or first if tie).
    pub fn winning_choice(&self, player_count: usize) -> usize {
        let mut counts = vec![0usize; self.options.len()];
        for vote in self.player_votes.iter().take(player_count).flatten() {
            if *vote < counts.len() {
                counts[*vote] += 1;
            }
        }
        counts.iter()
            .enumerate()
            .max_by_key(|(_, &count)| count)
            .map(|(idx, _)| idx)
            .unwrap_or(self.default_index)
    }
}

/// Cutscene playback state.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct CutsceneState {
    /// Cutscene ID.
    pub id: String,

    /// Current frame within the cutscene.
    pub frame: u32,

    /// Total duration in frames.
    pub duration: u32,

    /// Skip mode.
    pub skip_mode: SkipMode,

    /// Skip votes from each player.
    pub skip_votes: Vec<bool>,
}

impl CutsceneState {
    /// Check if cutscene should be skipped.
    pub fn should_skip(&self, player_count: usize) -> bool {
        match self.skip_mode {
            SkipMode::Unanimous => {
                self.skip_votes.iter().take(player_count).all(|&v| v)
            }
            SkipMode::HostDecides => {
                self.skip_votes.first().copied().unwrap_or(false)
            }
            SkipMode::Any => {
                self.skip_votes.iter().take(player_count).any(|&v| v)
            }
        }
    }
}

/// Cutscene skip mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Encode, Decode)]
pub enum SkipMode {
    /// All players must skip.
    Unanimous,
    /// Host (player 0) decides.
    HostDecides,
    /// Any player can skip.
    Any,
}

impl Default for SkipMode {
    fn default() -> Self {
        Self::Unanimous
    }
}

/// Transition state between segments.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct TransitionState {
    /// Segment we're leaving.
    pub from_segment: String,

    /// Segment we're entering.
    pub to_segment: String,

    /// Type of visual transition.
    pub transition_type: TransitionType,

    /// Total duration in frames.
    pub duration: u32,

    /// Elapsed frames.
    pub elapsed: u32,
}
