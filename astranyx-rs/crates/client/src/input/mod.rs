//! Input handling for the client.
//!
//! Converts platform input events to game inputs.

use astranyx_core::PlayerInput;
use winit::event::ElementState;
use winit::keyboard::{KeyCode, PhysicalKey};

/// Tracks current input state and converts to PlayerInput.
#[derive(Debug, Default)]
pub struct InputHandler {
    current: PlayerInput,
}

impl InputHandler {
    pub fn new() -> Self {
        Self::default()
    }

    /// Process a key event and update input state.
    pub fn process_key(&mut self, key: PhysicalKey, state: ElementState) {
        let pressed = state == ElementState::Pressed;

        let flag = match key {
            PhysicalKey::Code(KeyCode::KeyW) | PhysicalKey::Code(KeyCode::ArrowUp) => {
                Some(PlayerInput::UP)
            }
            PhysicalKey::Code(KeyCode::KeyS) | PhysicalKey::Code(KeyCode::ArrowDown) => {
                Some(PlayerInput::DOWN)
            }
            PhysicalKey::Code(KeyCode::KeyA) | PhysicalKey::Code(KeyCode::ArrowLeft) => {
                Some(PlayerInput::LEFT)
            }
            PhysicalKey::Code(KeyCode::KeyD) | PhysicalKey::Code(KeyCode::ArrowRight) => {
                Some(PlayerInput::RIGHT)
            }
            PhysicalKey::Code(KeyCode::Space) | PhysicalKey::Code(KeyCode::KeyZ) => {
                Some(PlayerInput::FIRE)
            }
            PhysicalKey::Code(KeyCode::KeyX) | PhysicalKey::Code(KeyCode::ControlLeft) => {
                Some(PlayerInput::SPECIAL)
            }
            PhysicalKey::Code(KeyCode::ShiftLeft) | PhysicalKey::Code(KeyCode::KeyC) => {
                Some(PlayerInput::FOCUS)
            }
            _ => None,
        };

        if let Some(flag) = flag {
            self.current.set(flag, pressed);
        }
    }

    /// Get the current input state.
    pub fn current(&self) -> PlayerInput {
        self.current
    }

    /// Reset all inputs (e.g., on focus loss).
    pub fn reset(&mut self) {
        self.current = PlayerInput::new();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn input_mapping() {
        let mut handler = InputHandler::new();

        // Press W
        handler.process_key(
            PhysicalKey::Code(KeyCode::KeyW),
            ElementState::Pressed,
        );
        assert!(handler.current().up());
        assert!(!handler.current().down());

        // Press Space
        handler.process_key(
            PhysicalKey::Code(KeyCode::Space),
            ElementState::Pressed,
        );
        assert!(handler.current().up());
        assert!(handler.current().fire());

        // Release W
        handler.process_key(
            PhysicalKey::Code(KeyCode::KeyW),
            ElementState::Released,
        );
        assert!(!handler.current().up());
        assert!(handler.current().fire());
    }
}
