//! Level loading and management.

use astranyx_physics::{CollisionWorld, ContentFlags};
use glam::Vec3;
use serde::{Deserialize, Serialize};

/// A game level containing collision geometry and spawn points.
#[derive(Debug)]
pub struct Level {
    /// Level identifier.
    pub id: String,

    /// Display name.
    pub name: String,

    /// Collision world for physics.
    pub collision: CollisionWorld,

    /// Player spawn points.
    pub spawn_points: Vec<SpawnPoint>,

    /// Light sources.
    pub lights: Vec<LightSource>,

    /// Trigger volumes.
    pub triggers: Vec<TriggerVolume>,
}

/// A spawn point for players or entities.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpawnPoint {
    /// Position in world space.
    pub position: Vec3,

    /// Initial facing direction (yaw in radians).
    pub facing: f32,

    /// Spawn point type.
    pub spawn_type: SpawnType,
}

/// Types of spawn points.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpawnType {
    /// Player spawn point.
    Player,
    /// Enemy spawn point.
    Enemy,
    /// Item spawn point.
    Item,
}

/// A light source in the level.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LightSource {
    /// Position in world space.
    pub position: Vec3,

    /// Light color (RGB, 0-1).
    pub color: Vec3,

    /// Light intensity.
    pub intensity: f32,

    /// Light range (for point/spot lights).
    pub range: f32,

    /// Light type.
    pub light_type: LightType,
}

/// Types of light sources.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LightType {
    /// Point light (omnidirectional).
    Point,
    /// Spot light (cone).
    Spot,
    /// Directional light (sun).
    Directional,
}

/// A trigger volume that fires events when entered.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TriggerVolume {
    /// Center position.
    pub position: Vec3,

    /// Half-extents of the trigger box.
    pub half_extents: Vec3,

    /// Trigger identifier for events.
    pub trigger_id: String,

    /// Whether this trigger can fire multiple times.
    pub repeatable: bool,

    /// Whether this trigger has been activated.
    pub activated: bool,
}

impl Level {
    /// Create an empty level.
    pub fn new(id: &str, name: &str) -> Self {
        Self {
            id: id.to_string(),
            name: name.to_string(),
            collision: CollisionWorld::new(),
            spawn_points: Vec::new(),
            lights: Vec::new(),
            triggers: Vec::new(),
        }
    }

    /// Create a simple test level for development.
    pub fn test_arena() -> Self {
        let mut level = Self::new("test_arena", "Test Arena");

        // Floor
        level.collision.add_box(
            Vec3::new(0.0, -0.5, 0.0),
            Vec3::new(50.0, 0.5, 50.0),
            ContentFlags::SOLID,
        );

        // Walls
        let wall_height = 5.0;
        let wall_thickness = 0.5;
        let arena_size = 50.0;

        // North wall
        level.collision.add_box(
            Vec3::new(0.0, wall_height / 2.0, -arena_size),
            Vec3::new(arena_size, wall_height / 2.0, wall_thickness),
            ContentFlags::SOLID,
        );

        // South wall
        level.collision.add_box(
            Vec3::new(0.0, wall_height / 2.0, arena_size),
            Vec3::new(arena_size, wall_height / 2.0, wall_thickness),
            ContentFlags::SOLID,
        );

        // East wall
        level.collision.add_box(
            Vec3::new(arena_size, wall_height / 2.0, 0.0),
            Vec3::new(wall_thickness, wall_height / 2.0, arena_size),
            ContentFlags::SOLID,
        );

        // West wall
        level.collision.add_box(
            Vec3::new(-arena_size, wall_height / 2.0, 0.0),
            Vec3::new(wall_thickness, wall_height / 2.0, arena_size),
            ContentFlags::SOLID,
        );

        // Central pillar
        level.collision.add_box(
            Vec3::new(0.0, 2.0, 0.0),
            Vec3::new(2.0, 2.0, 2.0),
            ContentFlags::SOLID,
        );

        // Some cover crates
        level.collision.add_box(
            Vec3::new(-15.0, 1.0, 10.0),
            Vec3::new(1.5, 1.0, 1.5),
            ContentFlags::SOLID,
        );
        level.collision.add_box(
            Vec3::new(15.0, 1.0, -10.0),
            Vec3::new(1.5, 1.0, 1.5),
            ContentFlags::SOLID,
        );

        // Spawn points
        level.spawn_points.push(SpawnPoint {
            position: Vec3::new(-20.0, 0.0, 0.0),
            facing: 0.0,
            spawn_type: SpawnType::Player,
        });
        level.spawn_points.push(SpawnPoint {
            position: Vec3::new(20.0, 0.0, 0.0),
            facing: std::f32::consts::PI,
            spawn_type: SpawnType::Player,
        });

        // Lights
        level.lights.push(LightSource {
            position: Vec3::new(0.0, 10.0, 0.0),
            color: Vec3::new(1.0, 0.95, 0.9),
            intensity: 2.0,
            range: 100.0,
            light_type: LightType::Point,
        });

        level
    }

    /// Get a player spawn point.
    pub fn get_player_spawn(&self, index: usize) -> Option<&SpawnPoint> {
        self.spawn_points
            .iter()
            .filter(|s| s.spawn_type == SpawnType::Player)
            .nth(index)
    }

    /// Get the number of player spawn points.
    pub fn player_spawn_count(&self) -> usize {
        self.spawn_points
            .iter()
            .filter(|s| s.spawn_type == SpawnType::Player)
            .count()
    }

    /// Check if a point is inside any trigger volume.
    pub fn check_triggers(&mut self, position: Vec3) -> Vec<String> {
        let mut triggered = Vec::new();

        for trigger in &mut self.triggers {
            if trigger.activated && !trigger.repeatable {
                continue;
            }

            let min = trigger.position - trigger.half_extents;
            let max = trigger.position + trigger.half_extents;

            if position.x >= min.x
                && position.x <= max.x
                && position.y >= min.y
                && position.y <= max.y
                && position.z >= min.z
                && position.z <= max.z
            {
                trigger.activated = true;
                triggered.push(trigger.trigger_id.clone());
            }
        }

        triggered
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_level_creation() {
        let level = Level::new("test", "Test Level");
        assert_eq!(level.id, "test");
        assert_eq!(level.collision.brush_count(), 0);
    }

    #[test]
    fn test_test_arena() {
        let level = Level::test_arena();
        assert!(level.collision.brush_count() > 0);
        assert!(level.player_spawn_count() >= 2);
    }

    #[test]
    fn test_trigger_check() {
        let mut level = Level::new("test", "Test");
        level.triggers.push(TriggerVolume {
            position: Vec3::new(0.0, 1.0, 0.0),
            half_extents: Vec3::new(2.0, 2.0, 2.0),
            trigger_id: "test_trigger".to_string(),
            repeatable: false,
            activated: false,
        });

        // Inside trigger
        let triggered = level.check_triggers(Vec3::new(0.0, 1.0, 0.0));
        assert_eq!(triggered.len(), 1);
        assert_eq!(triggered[0], "test_trigger");

        // Outside trigger
        let triggered = level.check_triggers(Vec3::new(10.0, 0.0, 0.0));
        assert!(triggered.is_empty());

        // Non-repeatable shouldn't fire again
        let triggered = level.check_triggers(Vec3::new(0.0, 1.0, 0.0));
        assert!(triggered.is_empty());
    }
}
