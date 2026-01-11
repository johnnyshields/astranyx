//! Debug HUD rendering with text display.

use three_d::*;

/// Debug HUD for displaying frame counter and game state.
pub struct DebugHud {
    text_generator: TextGenerator<'static>,
}

// Embed JetBrains Mono font (OFL license)
static FONT_BYTES: &[u8] = include_bytes!("../../assets/fonts/JetBrainsMono-Regular.ttf");

impl DebugHud {
    /// Create a new debug HUD.
    pub fn new() -> Result<Self, RendererError> {
        let text_generator = TextGenerator::new(FONT_BYTES, 0, 24.0)?;
        Ok(Self { text_generator })
    }

    /// Render debug information overlay.
    pub fn render(
        &self,
        context: &Context,
        frame_input: &mut FrameInput,
        frame: u32,
        segment_id: &str,
        mode: &str,
        frozen: bool,
        enemies: usize,
        bullets: usize,
    ) {
        let viewport = frame_input.viewport;

        // Build debug text
        let status = if frozen { "FROZEN" } else { "RUNNING" };
        let text = format!(
            "Frame: {}\nSegment: {}\nMode: {}\nStatus: {}\nEnemies: {}\nBullets: {}",
            frame, segment_id, mode, status, enemies, bullets
        );

        // Generate text mesh
        let cpu_mesh = self.text_generator.generate(&text, TextLayoutOptions::default());

        // Create 2D camera for overlay (origin at top-left)
        let camera = Camera::new_orthographic(
            viewport,
            vec3(viewport.width as f32 / 2.0, -(viewport.height as f32) / 2.0, 1.0),
            vec3(viewport.width as f32 / 2.0, -(viewport.height as f32) / 2.0, 0.0),
            vec3(0.0, 1.0, 0.0),
            viewport.height as f32,
            0.1,
            10.0,
        );

        // Create mesh and material
        let mut gm = Gm::new(
            Mesh::new(context, &cpu_mesh),
            ColorMaterial {
                color: Srgba::new(0, 255, 0, 255),  // Bright green for visibility
                ..Default::default()
            },
        );

        // Position at top-left with padding
        gm.set_transformation(Mat4::from_translation(vec3(10.0, -30.0, 0.0)));

        // Render
        frame_input.screen().render(&camera, &gm, &[]);
    }
}
