//! Player input handling.
//!
//! This module converts raw input (keyboard, mouse, gamepad) into
//! commands for the physics system.

use astranyx_physics::movement::{CommandButtons, PlayerCommand};
use serde::{Deserialize, Serialize};

/// Raw player input for a single frame.
///
/// This is the input format received from the client input system.
/// It gets converted to [`PlayerCommand`] for the physics system.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PlayerInput {
    /// Movement keys pressed.
    pub movement: MovementInput,

    /// Mouse delta this frame (pixels).
    pub mouse_delta: (f32, f32),

    /// Action buttons pressed.
    pub actions: ActionInput,

    /// Frame number this input was generated.
    pub frame: u32,
}

/// Movement key states.
#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize)]
pub struct MovementInput {
    pub forward: bool,
    pub backward: bool,
    pub left: bool,
    pub right: bool,
}

/// Action button states.
#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize)]
pub struct ActionInput {
    pub fire: bool,
    pub aim: bool,
    pub jump: bool,
    pub crouch: bool,
    pub sprint: bool,
    pub use_item: bool,
    pub reload: bool,
}

impl PlayerInput {
    /// Convert to a physics command.
    ///
    /// # Arguments
    ///
    /// * `mouse_sensitivity` - Mouse sensitivity multiplier
    pub fn to_command(&self, mouse_sensitivity: f32) -> PlayerCommand {
        let mut cmd = PlayerCommand::default();

        // Movement axes
        if self.movement.forward {
            cmd.forward_move += 1.0;
        }
        if self.movement.backward {
            cmd.forward_move -= 1.0;
        }
        if self.movement.right {
            cmd.right_move += 1.0;
        }
        if self.movement.left {
            cmd.right_move -= 1.0;
        }

        // Normalize diagonal movement
        let move_magnitude = (cmd.forward_move.powi(2) + cmd.right_move.powi(2)).sqrt();
        if move_magnitude > 1.0 {
            cmd.forward_move /= move_magnitude;
            cmd.right_move /= move_magnitude;
        }

        // View angles (convert mouse pixels to radians)
        // Negative X for yaw because moving mouse right should turn right (increase yaw)
        let sensitivity_radians = mouse_sensitivity * 0.001;
        cmd.view_delta = (
            -self.mouse_delta.1 * sensitivity_radians, // Pitch (Y mouse = pitch)
            self.mouse_delta.0 * sensitivity_radians,   // Yaw (X mouse = yaw)
        );

        // Action buttons
        if self.actions.fire {
            cmd.buttons.press(CommandButtons::ATTACK);
        }
        if self.actions.aim {
            cmd.buttons.press(CommandButtons::ATTACK2);
        }
        if self.actions.jump {
            cmd.buttons.press(CommandButtons::JUMP);
        }
        if self.actions.crouch {
            cmd.buttons.press(CommandButtons::CROUCH);
        }
        if self.actions.sprint {
            cmd.buttons.press(CommandButtons::SPRINT);
        }
        if self.actions.use_item {
            cmd.buttons.press(CommandButtons::USE);
        }
        if self.actions.reload {
            cmd.buttons.press(CommandButtons::RELOAD);
        }

        cmd
    }

    /// Check if any movement input is active.
    pub fn has_movement(&self) -> bool {
        self.movement.forward
            || self.movement.backward
            || self.movement.left
            || self.movement.right
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_input_to_command() {
        let mut input = PlayerInput::default();
        input.movement.forward = true;
        input.movement.right = true;
        input.actions.jump = true;

        let cmd = input.to_command(1.0);

        // Should be normalized for diagonal movement
        assert!(cmd.forward_move > 0.0 && cmd.forward_move < 1.0);
        assert!(cmd.right_move > 0.0 && cmd.right_move < 1.0);

        // Jump should be pressed
        assert!(cmd.buttons.pressed(CommandButtons::JUMP));
    }

    #[test]
    fn test_straight_movement_not_normalized() {
        let mut input = PlayerInput::default();
        input.movement.forward = true;

        let cmd = input.to_command(1.0);

        assert_eq!(cmd.forward_move, 1.0);
        assert_eq!(cmd.right_move, 0.0);
    }
}
