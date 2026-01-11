//! Sound propagation system for stealth gameplay.
//!
//! Different sounds have different radii and alert levels:
//! - Footsteps: Small radius, depends on surface and movement speed
//! - Gunfire: Large radius, immediately alerts nearby enemies
//! - Environmental: Doors, breaking glass, knockable objects
//! - Distractions: Thrown items, intentional noise
//!
//! Sound propagates through the environment, blocked by walls.

use glam::Vec3;

use crate::entities::EntityId;

/// Types of sounds that can alert enemies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SoundType {
    /// Player footsteps (affected by surface, speed, crouch)
    Footstep,
    /// Gunfire (very loud)
    Gunfire,
    /// Weapon impact (bullet hitting wall/object)
    Impact,
    /// Door opening/closing
    Door,
    /// Glass breaking
    GlassBreak,
    /// Object knocked over
    Knockover,
    /// Thrown distraction (magazine, rock, etc.)
    Distraction,
    /// Enemy death sound
    EnemyDeath,
    /// Voice/radio chatter
    Voice,
}

impl SoundType {
    /// Base loudness for this sound type (0.0-1.0).
    pub fn base_loudness(&self) -> f32 {
        match self {
            SoundType::Footstep => 0.2,
            SoundType::Gunfire => 1.0,
            SoundType::Impact => 0.4,
            SoundType::Door => 0.3,
            SoundType::GlassBreak => 0.7,
            SoundType::Knockover => 0.5,
            SoundType::Distraction => 0.6,
            SoundType::EnemyDeath => 0.5,
            SoundType::Voice => 0.3,
        }
    }

    /// Base radius for this sound type.
    pub fn base_radius(&self) -> f32 {
        match self {
            SoundType::Footstep => 30.0,
            SoundType::Gunfire => 500.0,
            SoundType::Impact => 80.0,
            SoundType::Door => 50.0,
            SoundType::GlassBreak => 150.0,
            SoundType::Knockover => 100.0,
            SoundType::Distraction => 120.0,
            SoundType::EnemyDeath => 100.0,
            SoundType::Voice => 60.0,
        }
    }

    /// Whether this sound type should draw enemies to investigate.
    pub fn attracts_investigation(&self) -> bool {
        match self {
            SoundType::Footstep => false, // Too common to investigate
            SoundType::Gunfire => true,
            SoundType::Impact => true,
            SoundType::Door => false, // Could be friendly
            SoundType::GlassBreak => true,
            SoundType::Knockover => true,
            SoundType::Distraction => true,
            SoundType::EnemyDeath => true,
            SoundType::Voice => false,
        }
    }
}

/// A sound event that can alert enemies.
#[derive(Debug, Clone)]
pub struct SoundEvent {
    /// World position of the sound
    pub position: Vec3,
    /// Type of sound
    pub sound_type: SoundType,
    /// Effective radius (may be modified from base)
    pub radius: f32,
    /// Entity that caused the sound (for attribution)
    pub source_entity: Option<EntityId>,
}

impl SoundEvent {
    /// Create a new sound event with default radius for the type.
    pub fn new(position: Vec3, sound_type: SoundType, source: Option<EntityId>) -> Self {
        Self {
            position,
            sound_type,
            radius: sound_type.base_radius(),
            source_entity: source,
        }
    }

    /// Create a footstep sound adjusted for movement state.
    pub fn footstep(position: Vec3, source: EntityId, is_running: bool, is_crouching: bool) -> Self {
        let base = SoundType::Footstep.base_radius();
        let radius = if is_crouching {
            base * 0.3 // Very quiet when crouching
        } else if is_running {
            base * 2.0 // Louder when running
        } else {
            base // Normal walking
        };

        Self {
            position,
            sound_type: SoundType::Footstep,
            radius,
            source_entity: Some(source),
        }
    }

    /// Calculate loudness at a given listener position.
    /// Returns 0.0 if out of range, up to base_loudness at the source.
    pub fn loudness_at(&self, listener_pos: Vec3) -> f32 {
        let distance = (listener_pos - self.position).length();
        if distance >= self.radius {
            return 0.0;
        }

        // Linear falloff
        let falloff = 1.0 - (distance / self.radius);
        self.sound_type.base_loudness() * falloff
    }

    /// Check if a listener at the given position can hear this sound.
    pub fn is_audible_at(&self, listener_pos: Vec3) -> bool {
        let distance = (listener_pos - self.position).length();
        distance < self.radius
    }
}

/// Surface type affects footstep sound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SurfaceType {
    #[default]
    Concrete,
    Metal,
    Grass,
    Water,
    Gravel,
    Wood,
    Carpet,
}

impl SurfaceType {
    /// Sound radius multiplier for this surface.
    pub fn sound_multiplier(&self) -> f32 {
        match self {
            SurfaceType::Concrete => 1.0,
            SurfaceType::Metal => 1.5,    // Very loud
            SurfaceType::Grass => 0.5,    // Quiet
            SurfaceType::Water => 1.2,    // Splashing
            SurfaceType::Gravel => 1.3,   // Crunchy
            SurfaceType::Wood => 0.9,
            SurfaceType::Carpet => 0.4,   // Very quiet
        }
    }
}

/// Process sound events and determine which enemies hear them.
/// Returns list of (enemy_index, sound_event, loudness) for enemies that heard sounds.
pub fn propagate_sounds(
    events: &[SoundEvent],
    enemy_positions: &[Vec3],
) -> Vec<(usize, SoundEvent, f32)> {
    let mut heard = Vec::new();

    for event in events {
        for (idx, &enemy_pos) in enemy_positions.iter().enumerate() {
            let loudness = event.loudness_at(enemy_pos);
            if loudness > 0.05 {
                // Minimum threshold to register
                heard.push((idx, event.clone(), loudness));
            }
        }
    }

    heard
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sound_falloff() {
        let event = SoundEvent::new(Vec3::ZERO, SoundType::Gunfire, None);

        // At source
        let loudness_0 = event.loudness_at(Vec3::ZERO);
        assert!((loudness_0 - 1.0).abs() < 0.01);

        // Half distance
        let loudness_half = event.loudness_at(Vec3::new(250.0, 0.0, 0.0));
        assert!((loudness_half - 0.5).abs() < 0.01);

        // At edge
        let loudness_edge = event.loudness_at(Vec3::new(500.0, 0.0, 0.0));
        assert!(loudness_edge < 0.01);

        // Beyond range
        let loudness_far = event.loudness_at(Vec3::new(600.0, 0.0, 0.0));
        assert_eq!(loudness_far, 0.0);
    }

    #[test]
    fn test_footstep_modifiers() {
        let pos = Vec3::ZERO;
        let id = EntityId(1);

        let normal = SoundEvent::footstep(pos, id, false, false);
        let running = SoundEvent::footstep(pos, id, true, false);
        let crouching = SoundEvent::footstep(pos, id, false, true);

        assert!(running.radius > normal.radius);
        assert!(crouching.radius < normal.radius);
    }

    #[test]
    fn test_sound_propagation() {
        let events = vec![SoundEvent::new(
            Vec3::new(0.0, 0.0, 0.0),
            SoundType::Gunfire,
            None,
        )];

        let enemy_positions = vec![
            Vec3::new(100.0, 0.0, 0.0),  // Close - should hear
            Vec3::new(600.0, 0.0, 0.0),  // Far - should not hear
        ];

        let heard = propagate_sounds(&events, &enemy_positions);
        assert_eq!(heard.len(), 1);
        assert_eq!(heard[0].0, 0); // First enemy
    }
}
