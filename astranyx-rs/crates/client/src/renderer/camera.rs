//! 2.5D Camera for Einhänder-style view.
//!
//! Camera is positioned in front of the play area (positive Z) and tilted
//! so the right side of the screen appears farther away.

use glam::{Mat4, Vec3};

/// Play bounds at the z=0 plane, accounting for perspective tilt.
pub struct PlayBounds {
    pub left_x: f32,
    pub right_x: f32,
    left_bottom_y: f32,
    left_top_y: f32,
    right_bottom_y: f32,
    right_top_y: f32,
}

impl PlayBounds {
    /// Get the top Y bound at a given X position (varies due to perspective).
    pub fn get_top_y(&self, x: f32) -> f32 {
        let t = (x - self.left_x) / (self.right_x - self.left_x);
        self.left_top_y + t * (self.right_top_y - self.left_top_y)
    }

    /// Get the bottom Y bound at a given X position (varies due to perspective).
    pub fn get_bottom_y(&self, x: f32) -> f32 {
        let t = (x - self.left_x) / (self.right_x - self.left_x);
        self.left_bottom_y + t * (self.right_bottom_y - self.left_bottom_y)
    }
}

/// 2.5D camera with Einhänder-style perspective tilt.
pub struct Camera {
    /// Camera distance from target.
    distance: f32,
    /// Tilt angle in radians (20° = right side farther away).
    tilt_angle: f32,
    /// Field of view in radians.
    fov: f32,
    /// Aspect ratio (width / height).
    aspect: f32,
    /// Near clipping plane.
    near: f32,
    /// Far clipping plane.
    far: f32,
    /// Target point the camera looks at.
    target: Vec3,

    // Cached matrices
    view_matrix: Mat4,
    projection_matrix: Mat4,
    position: Vec3,
}

impl Default for Camera {
    fn default() -> Self {
        Self::new()
    }
}

impl Camera {
    /// Create a new camera with default Einhänder-style settings.
    pub fn new() -> Self {
        let mut camera = Self {
            distance: 1500.0,
            tilt_angle: 20.0_f32.to_radians(),
            fov: 45.0_f32.to_radians(),
            aspect: 5.0 / 3.0,
            near: 10.0,
            far: 5000.0,
            target: Vec3::ZERO,
            view_matrix: Mat4::IDENTITY,
            projection_matrix: Mat4::IDENTITY,
            position: Vec3::ZERO,
        };
        camera.update_matrices();
        camera
    }

    /// Get the view matrix.
    pub fn view_matrix(&self) -> Mat4 {
        self.view_matrix
    }

    /// Get the projection matrix.
    pub fn projection_matrix(&self) -> Mat4 {
        self.projection_matrix
    }

    /// Get the combined view-projection matrix.
    pub fn view_projection_matrix(&self) -> Mat4 {
        self.projection_matrix * self.view_matrix
    }

    /// Get camera position.
    pub fn position(&self) -> Vec3 {
        self.position
    }

    /// Get camera distance from target.
    pub fn distance(&self) -> f32 {
        self.distance
    }

    /// Set camera distance.
    pub fn set_distance(&mut self, distance: f32) {
        self.distance = distance;
        self.update_matrices();
    }

    /// Get the target point.
    pub fn target(&self) -> Vec3 {
        self.target
    }

    /// Set the target point the camera looks at.
    pub fn set_target(&mut self, target: Vec3) {
        self.target = target;
        self.update_matrices();
    }

    /// Get tilt angle in radians.
    pub fn tilt_angle(&self) -> f32 {
        self.tilt_angle
    }

    /// Set tilt angle in radians.
    pub fn set_tilt_angle(&mut self, angle: f32) {
        self.tilt_angle = angle;
        self.update_matrices();
    }

    /// Set tilt angle in degrees.
    pub fn set_tilt_angle_degrees(&mut self, degrees: f32) {
        self.set_tilt_angle(degrees.to_radians());
    }

    /// Get field of view in radians.
    pub fn fov(&self) -> f32 {
        self.fov
    }

    /// Set field of view in radians.
    pub fn set_fov(&mut self, fov: f32) {
        self.fov = fov;
        self.update_matrices();
    }

    /// Set field of view in degrees.
    pub fn set_fov_degrees(&mut self, degrees: f32) {
        self.set_fov(degrees.to_radians());
    }

    /// Get aspect ratio.
    pub fn aspect(&self) -> f32 {
        self.aspect
    }

    /// Set aspect ratio.
    pub fn set_aspect(&mut self, aspect: f32) {
        self.aspect = aspect;
        self.update_matrices();
    }

    /// Set near/far clipping planes.
    pub fn set_clip_planes(&mut self, near: f32, far: f32) {
        self.near = near;
        self.far = far;
        self.update_matrices();
    }

    /// Update all matrices based on current settings.
    fn update_matrices(&mut self) {
        // Calculate camera position with tilt.
        // Camera is in front (positive Z) and slightly to the LEFT for Einhänder-style tilt.
        let offset = Vec3::new(
            -self.distance * self.tilt_angle.sin(),
            0.0,
            self.distance * self.tilt_angle.cos(),
        );
        self.position = self.target + offset;

        // Update view matrix (look at target).
        self.view_matrix = Mat4::look_at_rh(self.position, self.target, Vec3::Y);

        // Update projection matrix.
        self.projection_matrix =
            Mat4::perspective_rh(self.fov, self.aspect, self.near, self.far);
    }

    /// Project a world point to normalized device coordinates.
    pub fn world_to_ndc(&self, world_pos: Vec3) -> Vec3 {
        let vp = self.view_projection_matrix();
        let clip = vp * world_pos.extend(1.0);
        Vec3::new(clip.x / clip.w, clip.y / clip.w, clip.z / clip.w)
    }

    /// Unproject NDC point to world coordinates at z=0 plane.
    pub fn ndc_to_world(&self, ndc_x: f32, ndc_y: f32) -> (f32, f32) {
        let inv_vp = self.view_projection_matrix().inverse();

        // Create ray from near and far planes.
        let near_clip = inv_vp * glam::Vec4::new(ndc_x, ndc_y, -1.0, 1.0);
        let far_clip = inv_vp * glam::Vec4::new(ndc_x, ndc_y, 1.0, 1.0);

        let near_point = Vec3::new(
            near_clip.x / near_clip.w,
            near_clip.y / near_clip.w,
            near_clip.z / near_clip.w,
        );
        let far_point = Vec3::new(
            far_clip.x / far_clip.w,
            far_clip.y / far_clip.w,
            far_clip.z / far_clip.w,
        );

        // Find intersection with z=0 plane.
        let dz = far_point.z - near_point.z;
        if dz.abs() < 0.0001 {
            return (near_point.x, near_point.y);
        }

        let t = -near_point.z / dz;
        (
            near_point.x + t * (far_point.x - near_point.x),
            near_point.y + t * (far_point.y - near_point.y),
        )
    }

    /// Calculate the world-space play bounds visible in the viewport.
    /// Returns bounds at the z=0 plane accounting for perspective and tilt.
    pub fn get_play_bounds(&self) -> PlayBounds {
        // Unproject viewport corners to z=0 plane.
        let bottom_left = self.ndc_to_world(-1.0, -1.0);
        let bottom_right = self.ndc_to_world(1.0, -1.0);
        let top_right = self.ndc_to_world(1.0, 1.0);
        let top_left = self.ndc_to_world(-1.0, 1.0);

        let left_x = (bottom_left.0 + top_left.0) / 2.0;
        let right_x = (bottom_right.0 + top_right.0) / 2.0 - 100.0; // Buffer on right

        PlayBounds {
            left_x,
            right_x,
            left_bottom_y: bottom_left.1,
            left_top_y: top_left.1,
            right_bottom_y: bottom_right.1,
            right_top_y: top_right.1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_camera_defaults() {
        let camera = Camera::new();
        assert!((camera.distance() - 1500.0).abs() < 0.001);
        assert!((camera.tilt_angle() - 20.0_f32.to_radians()).abs() < 0.001);
        assert!((camera.fov() - 45.0_f32.to_radians()).abs() < 0.001);
        assert!((camera.aspect() - 5.0 / 3.0).abs() < 0.001);
        assert_eq!(camera.target(), Vec3::ZERO);
    }

    #[test]
    fn test_camera_position() {
        let camera = Camera::new();
        let pos = camera.position();
        // With 20° tilt, camera should be slightly left of center and in front
        assert!(pos.x < 0.0); // Left of center
        assert!((pos.y).abs() < 0.001); // No vertical offset
        assert!(pos.z > 0.0); // In front of origin
    }

    #[test]
    fn test_world_to_ndc_center() {
        let camera = Camera::new();
        let ndc = camera.world_to_ndc(Vec3::ZERO);
        // Origin should be near center of screen (not exactly due to tilt)
        assert!(ndc.x.abs() < 0.5);
        assert!(ndc.y.abs() < 0.5);
    }

    #[test]
    fn test_ndc_to_world_roundtrip() {
        let camera = Camera::new();
        let (x, y) = camera.ndc_to_world(0.0, 0.0);
        // Center of screen should map to near origin on z=0 plane
        assert!(x.abs() < 50.0);
        assert!(y.abs() < 50.0);
    }

    #[test]
    fn test_play_bounds() {
        let camera = Camera::new();
        let bounds = camera.get_play_bounds();
        // Left should be negative, right should be positive
        assert!(bounds.left_x < 0.0);
        assert!(bounds.right_x > 0.0);
        // Top should be above bottom
        assert!(bounds.get_top_y(0.0) > bounds.get_bottom_y(0.0));
    }
}
