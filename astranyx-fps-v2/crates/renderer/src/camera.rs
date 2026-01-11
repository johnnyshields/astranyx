//! First-person camera for rendering.

use glam::{Mat4, Vec3};

/// First-person camera state.
#[derive(Debug, Clone)]
pub struct FirstPersonCamera {
    /// Eye position in world space.
    pub position: Vec3,

    /// View angles (pitch, yaw, roll) in radians.
    pub angles: Vec3,

    /// Field of view in degrees.
    pub fov: f32,

    /// Near clipping plane.
    pub near: f32,

    /// Far clipping plane.
    pub far: f32,

    /// Aspect ratio (width / height).
    pub aspect: f32,
}

impl Default for FirstPersonCamera {
    fn default() -> Self {
        Self {
            position: Vec3::ZERO,
            angles: Vec3::ZERO,
            fov: 90.0,
            near: 0.1,
            far: 1000.0,
            aspect: 16.0 / 9.0,
        }
    }
}

impl FirstPersonCamera {
    /// Create a new camera at the given position.
    pub fn new(position: Vec3) -> Self {
        Self {
            position,
            ..Default::default()
        }
    }

    /// Get the view matrix for rendering.
    pub fn view_matrix(&self) -> Mat4 {
        let (sin_pitch, cos_pitch) = self.angles.x.sin_cos();
        let (sin_yaw, cos_yaw) = self.angles.y.sin_cos();

        // Forward direction (where we're looking)
        let forward = Vec3::new(
            cos_pitch * cos_yaw,
            -sin_pitch,
            cos_pitch * sin_yaw,
        );

        // Up direction
        let up = Vec3::Y;

        // Look at target
        let target = self.position + forward;

        Mat4::look_at_rh(self.position, target, up)
    }

    /// Get the projection matrix for rendering.
    pub fn projection_matrix(&self) -> Mat4 {
        Mat4::perspective_rh(
            self.fov.to_radians(),
            self.aspect,
            self.near,
            self.far,
        )
    }

    /// Get the combined view-projection matrix.
    pub fn view_projection_matrix(&self) -> Mat4 {
        self.projection_matrix() * self.view_matrix()
    }

    /// Get the forward direction vector.
    pub fn forward(&self) -> Vec3 {
        let (sin_pitch, cos_pitch) = self.angles.x.sin_cos();
        let (sin_yaw, cos_yaw) = self.angles.y.sin_cos();

        Vec3::new(
            cos_pitch * cos_yaw,
            -sin_pitch,
            cos_pitch * sin_yaw,
        )
    }

    /// Get the right direction vector.
    pub fn right(&self) -> Vec3 {
        let (sin_yaw, cos_yaw) = self.angles.y.sin_cos();
        Vec3::new(sin_yaw, 0.0, -cos_yaw)
    }

    /// Update camera from player state.
    pub fn update_from_player(
        &mut self,
        eye_position: Vec3,
        view_angles: Vec3,
    ) {
        self.position = eye_position;
        self.angles = view_angles;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_camera_creation() {
        let camera = FirstPersonCamera::new(Vec3::new(0.0, 1.6, 0.0));
        assert_eq!(camera.position.y, 1.6);
    }

    #[test]
    fn test_view_matrix() {
        let camera = FirstPersonCamera::default();
        let view = camera.view_matrix();

        // View matrix should be valid (non-zero determinant)
        assert!(view.determinant().abs() > 0.0001);
    }

    #[test]
    fn test_forward_direction() {
        let mut camera = FirstPersonCamera::default();

        // Yaw = 0 should point along +X
        camera.angles.y = 0.0;
        let forward = camera.forward();
        assert!((forward.x - 1.0).abs() < 0.01);

        // Yaw = PI/2 should point along +Z
        camera.angles.y = std::f32::consts::FRAC_PI_2;
        let forward = camera.forward();
        assert!((forward.z - 1.0).abs() < 0.01);
    }
}
