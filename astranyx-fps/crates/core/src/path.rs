//! Path/spline system for on-rails camera and player movement.
//!
//! Paths are defined in segment scripts and used for:
//! - On-rails shmup camera movement (Starfox-style)
//! - Turret/FPS on-rails sections
//! - Cinematic camera sequences

use bincode::{Decode, Encode};
use glam::{Quat, Vec3};
use serde::{Deserialize, Serialize};

/// A point on a path with position, rotation, and timing.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct PathPoint {
    /// World position at this point.
    #[bincode(with_serde)]
    pub position: Vec3,

    /// Orientation at this point (yaw/pitch stored as quaternion).
    #[bincode(with_serde)]
    pub rotation: Quat,

    /// Normalized time (0.0 to 1.0) when this point is reached.
    pub time: f32,
}

impl PathPoint {
    /// Create a new path point from position and euler angles (degrees).
    pub fn new(position: Vec3, yaw_deg: f32, pitch_deg: f32, time: f32) -> Self {
        let yaw = yaw_deg.to_radians();
        let pitch = pitch_deg.to_radians();

        // Create rotation: first yaw around Y, then pitch around X
        let rotation = Quat::from_rotation_y(yaw) * Quat::from_rotation_x(pitch);

        Self {
            position,
            rotation,
            time,
        }
    }

    /// Get euler angles in degrees (yaw, pitch).
    pub fn euler_degrees(&self) -> (f32, f32) {
        let (yaw, pitch, _roll) = self.rotation.to_euler(glam::EulerRot::YXZ);
        (yaw.to_degrees(), pitch.to_degrees())
    }
}

/// A path for on-rails movement, using Catmull-Rom spline interpolation.
#[derive(Debug, Clone, Serialize, Deserialize, Encode, Decode)]
pub struct Path {
    /// Unique identifier for this path.
    pub id: String,

    /// Control points defining the path.
    pub points: Vec<PathPoint>,

    /// Duration in frames to traverse the entire path.
    pub duration: u32,

    /// Whether the path loops back to the start.
    pub looping: bool,
}

impl Path {
    /// Create a new path with the given ID and duration.
    pub fn new(id: &str, duration: u32) -> Self {
        Self {
            id: id.to_string(),
            points: Vec::new(),
            duration,
            looping: false,
        }
    }

    /// Add a point to the path.
    pub fn add_point(&mut self, point: PathPoint) {
        self.points.push(point);
    }

    /// Sample the path at normalized time t (0.0 to 1.0).
    /// Returns (position, rotation) using Catmull-Rom interpolation.
    pub fn sample(&self, t: f32) -> (Vec3, Quat) {
        if self.points.is_empty() {
            return (Vec3::ZERO, Quat::IDENTITY);
        }

        if self.points.len() == 1 {
            return (self.points[0].position, self.points[0].rotation);
        }

        // Clamp t to valid range
        let t = if self.looping {
            t.rem_euclid(1.0)
        } else {
            t.clamp(0.0, 1.0)
        };

        // Find the segment containing t
        let mut i1 = 0;
        for (i, point) in self.points.iter().enumerate() {
            if point.time > t {
                break;
            }
            i1 = i;
        }

        let i2 = (i1 + 1).min(self.points.len() - 1);

        // Get the four points for Catmull-Rom
        let i0 = if i1 == 0 { 0 } else { i1 - 1 };
        let i3 = (i2 + 1).min(self.points.len() - 1);

        let p0 = &self.points[i0];
        let p1 = &self.points[i1];
        let p2 = &self.points[i2];
        let p3 = &self.points[i3];

        // Calculate local t within this segment
        let segment_t = if p2.time == p1.time {
            0.0
        } else {
            (t - p1.time) / (p2.time - p1.time)
        };

        // Catmull-Rom position interpolation
        let position = catmull_rom_vec3(
            p0.position,
            p1.position,
            p2.position,
            p3.position,
            segment_t,
        );

        // Spherical interpolation for rotation (simpler, just use slerp)
        let rotation = p1.rotation.slerp(p2.rotation, segment_t);

        (position, rotation)
    }

    /// Sample the path at a given frame.
    pub fn sample_at_frame(&self, frame: u32) -> (Vec3, Quat) {
        if self.duration == 0 {
            return self.sample(0.0);
        }
        let t = frame as f32 / self.duration as f32;
        self.sample(t)
    }

    /// Get the forward direction at normalized time t.
    pub fn forward_at(&self, t: f32) -> Vec3 {
        let (_, rotation) = self.sample(t);
        rotation * Vec3::NEG_Z // Forward is -Z in our coordinate system
    }

    /// Get total path length (approximate, by sampling).
    pub fn approximate_length(&self, samples: usize) -> f32 {
        if self.points.len() < 2 {
            return 0.0;
        }

        let mut length = 0.0;
        let mut prev_pos = self.sample(0.0).0;

        for i in 1..=samples {
            let t = i as f32 / samples as f32;
            let pos = self.sample(t).0;
            length += (pos - prev_pos).length();
            prev_pos = pos;
        }

        length
    }
}

/// Catmull-Rom spline interpolation for Vec3.
fn catmull_rom_vec3(p0: Vec3, p1: Vec3, p2: Vec3, p3: Vec3, t: f32) -> Vec3 {
    let t2 = t * t;
    let t3 = t2 * t;

    // Catmull-Rom basis matrix coefficients
    let c0 = -0.5 * t3 + t2 - 0.5 * t;
    let c1 = 1.5 * t3 - 2.5 * t2 + 1.0;
    let c2 = -1.5 * t3 + 2.0 * t2 + 0.5 * t;
    let c3 = 0.5 * t3 - 0.5 * t2;

    p0 * c0 + p1 * c1 + p2 * c2 + p3 * c3
}

/// Path collection for a segment.
#[derive(Debug, Clone, Default)]
pub struct PathSet {
    paths: Vec<Path>,
}

impl PathSet {
    pub fn new() -> Self {
        Self { paths: Vec::new() }
    }

    pub fn add(&mut self, path: Path) {
        self.paths.push(path);
    }

    pub fn get(&self, id: &str) -> Option<&Path> {
        self.paths.iter().find(|p| p.id == id)
    }

    pub fn clear(&mut self) {
        self.paths.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_linear() {
        let mut path = Path::new("test", 60);
        path.add_point(PathPoint::new(Vec3::new(0.0, 0.0, 0.0), 0.0, 0.0, 0.0));
        path.add_point(PathPoint::new(Vec3::new(100.0, 0.0, 0.0), 0.0, 0.0, 1.0));

        let (pos, _rot) = path.sample(0.0);
        assert!((pos.x - 0.0).abs() < 0.01);

        let (pos, _rot) = path.sample(0.5);
        assert!((pos.x - 50.0).abs() < 1.0); // Catmull-Rom may not be exactly 50

        let (pos, _rot) = path.sample(1.0);
        assert!((pos.x - 100.0).abs() < 0.01);
    }

    #[test]
    fn test_path_rotation() {
        let mut path = Path::new("test", 60);
        path.add_point(PathPoint::new(Vec3::ZERO, 0.0, 0.0, 0.0));
        path.add_point(PathPoint::new(Vec3::ZERO, 90.0, 0.0, 1.0));

        let (_pos, rot) = path.sample(0.5);
        let (yaw, _pitch) = {
            let (y, p, _r) = rot.to_euler(glam::EulerRot::YXZ);
            (y.to_degrees(), p.to_degrees())
        };

        // Should be approximately 45 degrees
        assert!((yaw - 45.0).abs() < 5.0);
    }

    #[test]
    fn test_frame_sampling() {
        let mut path = Path::new("test", 60);
        path.add_point(PathPoint::new(Vec3::new(0.0, 0.0, 0.0), 0.0, 0.0, 0.0));
        path.add_point(PathPoint::new(Vec3::new(60.0, 0.0, 0.0), 0.0, 0.0, 1.0));

        let (pos, _rot) = path.sample_at_frame(30);
        // At frame 30/60, should be roughly at x=30
        assert!((pos.x - 30.0).abs() < 5.0);
    }
}
