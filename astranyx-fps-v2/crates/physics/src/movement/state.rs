//! Movement state and input structures.

use glam::Vec3;
use serde::{Deserialize, Serialize};

use super::jump::JumpState;
use super::stance::{Stance, StanceState};

/// Flags describing the player's current movement state.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MovementFlags(pub u16);

impl MovementFlags {
    /// Player is touching the ground.
    pub const ON_GROUND: u16 = 1 << 0;

    /// Player is jumping (recently left ground via jump).
    pub const JUMPING: u16 = 1 << 1;

    /// Player is crouching/ducking.
    pub const CROUCHING: u16 = 1 << 2;

    /// Player is prone (lying down).
    pub const PRONE: u16 = 1 << 3;

    /// Player is sprinting.
    pub const SPRINTING: u16 = 1 << 4;

    /// Player is in water.
    pub const IN_WATER: u16 = 1 << 5;

    /// Player is swimming (fully submerged).
    pub const SWIMMING: u16 = 1 << 6;

    /// Player is on a ladder.
    pub const ON_LADDER: u16 = 1 << 7;

    /// Player is dead.
    pub const DEAD: u16 = 1 << 8;

    /// Player is frozen (can't move).
    pub const FROZEN: u16 = 1 << 9;

    /// Player is noclipping (ignores collision).
    pub const NOCLIP: u16 = 1 << 10;

    /// Check if a flag is set.
    #[inline]
    pub fn has(self, flag: u16) -> bool {
        (self.0 & flag) != 0
    }

    /// Set or clear a flag.
    #[inline]
    pub fn set(&mut self, flag: u16, value: bool) {
        if value {
            self.0 |= flag;
        } else {
            self.0 &= !flag;
        }
    }

    /// Check if player is on the ground.
    #[inline]
    pub fn on_ground(self) -> bool {
        self.has(Self::ON_GROUND)
    }

    /// Check if player is crouching.
    #[inline]
    pub fn crouching(self) -> bool {
        self.has(Self::CROUCHING)
    }

    /// Check if player is prone.
    #[inline]
    pub fn prone(self) -> bool {
        self.has(Self::PRONE)
    }

    /// Check if player is sprinting.
    #[inline]
    pub fn sprinting(self) -> bool {
        self.has(Self::SPRINTING)
    }

    /// Check if player is jumping.
    #[inline]
    pub fn jumping(self) -> bool {
        self.has(Self::JUMPING)
    }

    /// Check if player can move.
    #[inline]
    pub fn can_move(self) -> bool {
        !self.has(Self::DEAD) && !self.has(Self::FROZEN)
    }
}

/// Complete movement state for a player.
///
/// This contains everything needed to simulate player movement:
/// - Position and velocity
/// - View angles
/// - Movement flags (on ground, crouching, etc.)
/// - Timers for cooldowns
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MovementState {
    /// Position in world space (feet/bottom of collision shape).
    pub position: Vec3,

    /// Velocity in world space (meters/second).
    pub velocity: Vec3,

    /// View angles in radians: (pitch, yaw, roll).
    ///
    /// - Pitch: Looking up/down (-PI/2 to PI/2)
    /// - Yaw: Looking left/right (-PI to PI)
    /// - Roll: Tilting head (usually 0)
    pub view_angles: Vec3,

    /// Movement state flags.
    pub flags: MovementFlags,

    /// Stance state machine (handles crouch/prone with toggle/hold).
    pub stance: StanceState,

    /// Jump state machine (handles cooldown and queuing).
    pub jump: JumpState,

    /// Ground entity ID (-1 if airborne, 0 for world, >0 for moving platform).
    pub ground_entity: i32,

    /// Ground surface normal (valid when on_ground is true).
    pub ground_normal: Vec3,

    /// Current crouch amount (0.0 = standing, 1.0 = fully crouched).
    /// Used for smooth crouch transitions.
    pub crouch_fraction: f32,

    /// Current prone amount (0.0 = not prone, 1.0 = fully prone).
    /// Used for smooth prone transitions.
    pub prone_fraction: f32,
}

impl Default for MovementState {
    fn default() -> Self {
        Self {
            position: Vec3::ZERO,
            velocity: Vec3::ZERO,
            view_angles: Vec3::ZERO,
            flags: MovementFlags::default(),
            stance: StanceState::default(),
            jump: JumpState::default(),
            ground_entity: -1,
            ground_normal: Vec3::Y,
            crouch_fraction: 0.0,
            prone_fraction: 0.0,
        }
    }
}

impl MovementState {
    /// Create a new movement state at the given position.
    pub fn new(position: Vec3) -> Self {
        Self {
            position,
            ..Default::default()
        }
    }

    /// Sync movement flags to match stance state.
    /// Call this after updating stance to keep flags in sync.
    pub fn sync_flags_from_stance(&mut self) {
        self.flags.set(MovementFlags::CROUCHING, self.stance.is_crouching());
        self.flags.set(MovementFlags::PRONE, self.stance.is_prone());
    }

    /// Get the eye position (for camera placement).
    pub fn eye_position(
        &self,
        standing_eye_height: f32,
        crouching_eye_height: f32,
        prone_eye_height: f32,
    ) -> Vec3 {
        // Blend eye height using both fractions for smooth transitions
        // This ensures Prone->Crouch doesn't flash through Standing
        //
        // prone_fraction: 0 = not prone, 1 = fully prone
        // crouch_fraction: 0 = not crouched, 1 = fully crouched
        //
        // First blend between standing and crouching based on crouch_fraction
        let standing_crouch_blend =
            standing_eye_height * (1.0 - self.crouch_fraction) +
            crouching_eye_height * self.crouch_fraction;

        // Then blend that result toward prone based on prone_fraction
        let eye_height =
            standing_crouch_blend * (1.0 - self.prone_fraction) +
            prone_eye_height * self.prone_fraction;

        self.position + Vec3::new(0.0, eye_height, 0.0)
    }

    /// Get the forward direction from view angles (horizontal only).
    pub fn forward_direction(&self) -> Vec3 {
        let (sin_yaw, cos_yaw) = self.view_angles.y.sin_cos();
        Vec3::new(cos_yaw, 0.0, sin_yaw).normalize()
    }

    /// Get the right direction from view angles (horizontal only).
    pub fn right_direction(&self) -> Vec3 {
        let (sin_yaw, cos_yaw) = self.view_angles.y.sin_cos();
        Vec3::new(-sin_yaw, 0.0, cos_yaw).normalize()
    }

    /// Get the full forward direction including pitch.
    pub fn look_direction(&self) -> Vec3 {
        let (sin_pitch, cos_pitch) = self.view_angles.x.sin_cos();
        let (sin_yaw, cos_yaw) = self.view_angles.y.sin_cos();

        Vec3::new(
            cos_pitch * cos_yaw,
            -sin_pitch,
            cos_pitch * sin_yaw,
        )
    }

    /// Get current horizontal speed.
    pub fn horizontal_speed(&self) -> f32 {
        Vec3::new(self.velocity.x, 0.0, self.velocity.z).length()
    }

    /// Check if moving (has significant velocity).
    pub fn is_moving(&self) -> bool {
        self.velocity.length_squared() > 0.01
    }
}

/// Input command from the player for a single frame.
///
/// This represents the player's intent - what buttons they pressed
/// and how they moved the mouse.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PlayerCommand {
    /// Forward/backward movement (-1.0 to 1.0).
    /// Positive = forward, negative = backward.
    pub forward_move: f32,

    /// Strafe left/right (-1.0 to 1.0).
    /// Positive = right, negative = left.
    pub right_move: f32,

    /// View angle delta this frame (radians).
    /// (pitch_delta, yaw_delta)
    pub view_delta: (f32, f32),

    /// Button states.
    pub buttons: CommandButtons,
}

/// Button state flags for player commands.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommandButtons(pub u16);

impl CommandButtons {
    /// Primary attack/fire button.
    pub const ATTACK: u16 = 1 << 0;

    /// Secondary attack/aim button.
    pub const ATTACK2: u16 = 1 << 1;

    /// Jump button.
    pub const JUMP: u16 = 1 << 2;

    /// Crouch button.
    pub const CROUCH: u16 = 1 << 3;

    /// Prone button.
    pub const PRONE: u16 = 1 << 4;

    /// Sprint button.
    pub const SPRINT: u16 = 1 << 5;

    /// Use/interact button.
    pub const USE: u16 = 1 << 6;

    /// Reload button.
    pub const RELOAD: u16 = 1 << 7;

    /// Walk (slow movement) button.
    pub const WALK: u16 = 1 << 8;

    /// Check if a button is pressed.
    #[inline]
    pub fn pressed(self, button: u16) -> bool {
        (self.0 & button) != 0
    }

    /// Press a button.
    #[inline]
    pub fn press(&mut self, button: u16) {
        self.0 |= button;
    }

    /// Release a button.
    #[inline]
    pub fn release(&mut self, button: u16) {
        self.0 &= !button;
    }
}

impl PlayerCommand {
    /// Check if jump is requested.
    #[inline]
    pub fn wants_jump(&self) -> bool {
        self.buttons.pressed(CommandButtons::JUMP)
    }

    /// Check if crouch is requested.
    #[inline]
    pub fn wants_crouch(&self) -> bool {
        self.buttons.pressed(CommandButtons::CROUCH)
    }

    /// Check if prone is requested.
    #[inline]
    pub fn wants_prone(&self) -> bool {
        self.buttons.pressed(CommandButtons::PRONE)
    }

    /// Check if sprint is requested.
    #[inline]
    pub fn wants_sprint(&self) -> bool {
        self.buttons.pressed(CommandButtons::SPRINT)
    }

    /// Check if any movement input is active.
    #[inline]
    pub fn has_movement_input(&self) -> bool {
        self.forward_move.abs() > 0.01 || self.right_move.abs() > 0.01
    }

    /// Get normalized movement direction in local space.
    pub fn movement_direction(&self) -> Vec3 {
        let dir = Vec3::new(self.right_move, 0.0, self.forward_move);
        if dir.length_squared() > 0.01 {
            dir.normalize()
        } else {
            Vec3::ZERO
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::f32::consts::PI;

    #[test]
    fn test_movement_flags() {
        let mut flags = MovementFlags::default();
        assert!(!flags.on_ground());

        flags.set(MovementFlags::ON_GROUND, true);
        assert!(flags.on_ground());

        flags.set(MovementFlags::ON_GROUND, false);
        assert!(!flags.on_ground());
    }

    #[test]
    fn test_movement_state_directions() {
        let mut state = MovementState::new(Vec3::ZERO);

        // Facing +Z (yaw = 0)
        state.view_angles.y = 0.0;
        let forward = state.forward_direction();
        assert!((forward.x - 1.0).abs() < 0.01);
        assert!(forward.z.abs() < 0.01);

        // Facing +X (yaw = PI/2)
        state.view_angles.y = PI / 2.0;
        let forward = state.forward_direction();
        assert!(forward.x.abs() < 0.01);
        assert!((forward.z - 1.0).abs() < 0.01);
    }

    #[test]
    fn test_player_command_buttons() {
        let mut cmd = PlayerCommand::default();
        assert!(!cmd.wants_jump());

        cmd.buttons.press(CommandButtons::JUMP);
        assert!(cmd.wants_jump());
    }
}
