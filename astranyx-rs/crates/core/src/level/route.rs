//! Route definitions and trigger evaluation.
//!
//! Routes connect segments and define when transitions occur.

use bincode::{Decode, Encode};
use serde::{Deserialize, Serialize};

/// A route connecting two segments.
#[derive(Debug, Clone)]
pub struct Route {
    /// Source segment ID.
    pub from: String,

    /// Destination segment ID.
    pub to: String,

    /// Trigger condition for this route.
    pub trigger: RouteTrigger,

    /// Transition effect.
    pub transition: Transition,

    /// Priority (higher = checked first).
    pub priority: i32,
}

impl Route {
    /// Whether this is a player choice route.
    pub fn is_choice(&self) -> bool {
        matches!(self.trigger, RouteTrigger::Choice { .. })
    }

    /// Evaluate this route's trigger against the current level state.
    pub fn evaluate(&self, level: &super::LevelState) -> bool {
        match &self.trigger {
            RouteTrigger::Distance { value } => level.scroll_offset.x >= *value,
            RouteTrigger::Time { frames } => level.segment_frame >= *frames,
            RouteTrigger::EnemiesKilled { count } => level.enemies_killed >= *count,
            RouteTrigger::BossDefeated => level.boss_defeated,
            RouteTrigger::Bonus { condition } => self.evaluate_bonus(condition, level),
            RouteTrigger::Choice { .. } => false, // Handled separately via pending_choice
            RouteTrigger::Immediate => true,
        }
    }

    /// Evaluate a bonus condition against the level state.
    fn evaluate_bonus(&self, condition: &str, level: &super::LevelState) -> bool {
        match condition {
            "secret_path_found" => level.secrets_found > 0,
            "all_enemies_killed" => level.enemies_spawned > 0 && level.enemies_killed >= level.enemies_spawned,
            "no_damage" => level.damage_taken == 0,
            _ => false,
        }
    }
}

/// Trigger condition for a route.
#[derive(Debug, Clone)]
pub enum RouteTrigger {
    /// Trigger after traveling a certain distance (scroll offset).
    Distance {
        value: f32,
    },

    /// Trigger after a certain number of frames in the segment.
    Time {
        frames: u32,
    },

    /// Trigger after killing a certain number of enemies.
    EnemiesKilled {
        count: u32,
    },

    /// Trigger when the boss is defeated.
    BossDefeated,

    /// Trigger based on a custom condition.
    Bonus {
        /// Condition name to evaluate in script.
        condition: String,
    },

    /// Player choice prompt.
    Choice {
        /// Prompt text to display.
        prompt: String,
        /// Timeout in frames before auto-selecting.
        timeout: u32,
        /// Default choice index on timeout.
        default: usize,
    },

    /// Trigger immediately (for chaining).
    Immediate,
}

impl RouteTrigger {
    /// Parse from script map.
    pub fn from_map(map: &rhai::Map) -> Option<Self> {
        let trigger_type = map.get("type")?.clone().into_string().ok()?;

        Some(match trigger_type.as_str() {
            "distance" => Self::Distance {
                value: map.get("value")?.as_float().ok()? as f32,
            },
            "time" => Self::Time {
                frames: map.get("value")?.as_int().ok()? as u32,
            },
            "enemies_killed" => Self::EnemiesKilled {
                count: map.get("value")?.as_int().ok()? as u32,
            },
            "boss_defeated" => Self::BossDefeated,
            "bonus" => Self::Bonus {
                condition: map.get("condition")?.clone().into_string().ok()?,
            },
            "choice" => Self::Choice {
                prompt: map.get("prompt")
                    .and_then(|v| v.clone().into_string().ok())
                    .unwrap_or_else(|| "Choose your path".to_string()),
                timeout: map.get("timeout")
                    .and_then(|v| v.as_int().ok())
                    .unwrap_or(300) as u32,
                default: map.get("default")
                    .and_then(|v| v.as_int().ok())
                    .unwrap_or(0) as usize,
            },
            "immediate" => Self::Immediate,
            _ => return None,
        })
    }
}

/// Transition effect between segments.
#[derive(Debug, Clone)]
pub struct Transition {
    /// Type of visual transition.
    pub transition_type: TransitionType,

    /// Duration in frames.
    pub duration: u32,

    /// Optional cutscene to play.
    pub cutscene: Option<String>,
}

impl Default for Transition {
    fn default() -> Self {
        Self {
            transition_type: TransitionType::Fade,
            duration: 30,
            cutscene: None,
        }
    }
}

/// Visual transition types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Encode, Decode)]
pub enum TransitionType {
    /// Instant cut.
    Instant,
    /// Fade to black and back.
    Fade,
    /// Horizontal wipe.
    WipeHorizontal,
    /// Vertical wipe.
    WipeVertical,
    /// Circular wipe.
    WipeCircle,
    /// Crossfade (both segments visible briefly).
    Crossfade,
}

impl Default for TransitionType {
    fn default() -> Self {
        Self::Fade
    }
}

impl TransitionType {
    /// Parse from script string.
    pub fn from_string(s: &str) -> Self {
        match s {
            "instant" => Self::Instant,
            "fade" => Self::Fade,
            "wipe" | "wipe_horizontal" => Self::WipeHorizontal,
            "wipe_vertical" => Self::WipeVertical,
            "wipe_circle" => Self::WipeCircle,
            "crossfade" => Self::Crossfade,
            _ => Self::Fade,
        }
    }
}

/// Route evaluation result.
#[derive(Debug, Clone)]
pub enum RouteResult {
    /// No route triggered.
    None,
    /// Route triggered, transition to segment.
    Transition {
        to_segment: String,
        transition: Transition,
    },
    /// Player choice needed.
    Choice {
        options: Vec<String>,
        prompt: String,
        timeout: u32,
        default: usize,
    },
}

/// Evaluate a route trigger against the current level state.
pub fn evaluate_trigger(
    trigger: &RouteTrigger,
    segment_frame: u32,
    scroll_offset: f32,
    enemies_killed: u32,
    boss_defeated: bool,
    custom_conditions: &dyn Fn(&str) -> bool,
) -> bool {
    match trigger {
        RouteTrigger::Distance { value } => scroll_offset >= *value,
        RouteTrigger::Time { frames } => segment_frame >= *frames,
        RouteTrigger::EnemiesKilled { count } => enemies_killed >= *count,
        RouteTrigger::BossDefeated => boss_defeated,
        RouteTrigger::Bonus { condition } => custom_conditions(condition),
        RouteTrigger::Choice { .. } => false, // Handled separately
        RouteTrigger::Immediate => true,
    }
}
