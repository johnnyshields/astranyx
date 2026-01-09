//! Application state and event loop handler.

use std::sync::Arc;
use std::time::Instant;

use winit::{
    application::ApplicationHandler,
    dpi::PhysicalSize,
    event::WindowEvent,
    event_loop::ActiveEventLoop,
    window::{Window, WindowId},
};

use astranyx_core::input::PlayerInput;
use astranyx_core::simulation::{Simulation, SimulationConfig};

use crate::game;
use crate::renderer::Renderer;

/// Main application state.
pub struct App {
    window: Option<Arc<Window>>,
    renderer: Option<Renderer>,
    simulation: Option<Simulation>,
    last_frame_time: Option<Instant>,
    accumulated_time: f32,
    meshes_registered: bool,
}

impl App {
    /// Simulation tick rate (30 Hz).
    const TICK_RATE: u32 = 30;
    /// Seconds per simulation tick.
    const TICK_DURATION: f32 = 1.0 / 30.0;

    pub fn new() -> Self {
        Self {
            window: None,
            renderer: None,
            simulation: None,
            last_frame_time: None,
            accumulated_time: 0.0,
            meshes_registered: false,
        }
    }

    /// Set the renderer (used by WASM async init).
    pub fn set_renderer(&mut self, renderer: Renderer) {
        self.renderer = Some(renderer);
    }

    /// Get window reference.
    pub fn window(&self) -> Option<&Arc<Window>> {
        self.window.as_ref()
    }

    #[cfg(feature = "native")]
    fn init_window(&mut self, event_loop: &ActiveEventLoop) {
        let window_attrs = Window::default_attributes()
            .with_title("Astranyx")
            .with_inner_size(PhysicalSize::new(1280, 720));

        let window = Arc::new(
            event_loop
                .create_window(window_attrs)
                .expect("failed to create window"),
        );

        // Initialize renderer synchronously on native
        let mut renderer = pollster::block_on(Renderer::new(window.clone()))
            .expect("failed to create renderer");

        // Set camera to look at center of game world (0-1920 x 0-1080)
        // With 60° FOV, we need distance ~ height / (2 * tan(30°)) = 1080 / 1.155 ≈ 935
        // Use 1400 for some margin
        let camera = renderer.camera_mut();
        camera.set_target(glam::Vec3::new(960.0, 540.0, 0.0));
        camera.set_tilt_angle(0.0); // No tilt for now - easier to debug
        camera.set_fov_degrees(60.0); // Wider FOV to see more
        camera.set_distance(1400.0);
        camera.set_clip_planes(10.0, 5000.0);

        // Register game meshes
        game::register_meshes(&mut renderer);
        self.meshes_registered = true;

        // Initialize simulation
        let config = SimulationConfig::default();
        let simulation = Simulation::new(config, 12345, 1); // Single player for now
        self.simulation = Some(simulation);

        self.window = Some(window);
        self.renderer = Some(renderer);
        self.last_frame_time = Some(Instant::now());

        tracing::info!("Window, renderer, and simulation initialized");
    }

    #[cfg(feature = "wasm")]
    fn init_window(&mut self, event_loop: &ActiveEventLoop) {
        use winit::platform::web::WindowAttributesExtWebSys;

        let window_attrs = Window::default_attributes()
            .with_title("Astranyx")
            .with_canvas(get_canvas());

        let window = Arc::new(
            event_loop
                .create_window(window_attrs)
                .expect("failed to create window"),
        );

        self.window = Some(window);
        tracing::info!("Window initialized");
    }
}

#[cfg(feature = "wasm")]
fn get_canvas() -> Option<web_sys::HtmlCanvasElement> {
    use wasm_bindgen::JsCast;
    let window = web_sys::window()?;
    let document = window.document()?;
    let canvas = document.get_element_by_id("astranyx-canvas")?;
    canvas.dyn_into::<web_sys::HtmlCanvasElement>().ok()
}

impl App {
    /// Render a single frame.
    fn render_frame(&mut self, delta_time: f32) -> Result<(), wgpu::SurfaceError> {
        // Take simulation state snapshot for rendering
        let sim_state = self.simulation.as_ref().map(|s| s.state.clone());

        let renderer = match &mut self.renderer {
            Some(r) => r,
            None => return Ok(()),
        };

        renderer.begin_frame(delta_time);

        let output = renderer.surface().get_current_texture()?;
        let view = output
            .texture
            .create_view(&wgpu::TextureViewDescriptor::default());

        let mut encoder = renderer
            .device()
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("render_encoder"),
            });

        // Clear pass
        {
            let _render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("clear_pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: &view,
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Clear(wgpu::Color {
                            r: 0.02,
                            g: 0.02,
                            b: 0.06,
                            a: 1.0,
                        }),
                        store: wgpu::StoreOp::Store,
                    },
                })],
                depth_stencil_attachment: Some(wgpu::RenderPassDepthStencilAttachment {
                    view: renderer.depth_view(),
                    depth_ops: Some(wgpu::Operations {
                        load: wgpu::LoadOp::Clear(1.0),
                        store: wgpu::StoreOp::Store,
                    }),
                    stencil_ops: None,
                }),
                timestamp_writes: None,
                occlusion_query_set: None,
            });
        }

        // Render game entities
        if let Some(state) = &sim_state {
            game::render_game_state(renderer, state, &mut encoder, &view);
        }

        renderer.queue().submit(std::iter::once(encoder.finish()));
        output.present();

        Ok(())
    }
}

impl Default for App {
    fn default() -> Self {
        Self::new()
    }
}

impl ApplicationHandler for App {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        if self.window.is_none() {
            self.init_window(event_loop);
        }
    }

    fn window_event(&mut self, event_loop: &ActiveEventLoop, _id: WindowId, event: WindowEvent) {
        match event {
            WindowEvent::CloseRequested => {
                tracing::info!("Close requested, exiting");
                event_loop.exit();
            }

            WindowEvent::Resized(new_size) => {
                if let Some(renderer) = &mut self.renderer {
                    renderer.resize(new_size);
                }
            }

            WindowEvent::RedrawRequested => {
                // Calculate delta time
                let now = Instant::now();
                let delta_time = if let Some(last) = self.last_frame_time {
                    now.duration_since(last).as_secs_f32()
                } else {
                    Self::TICK_DURATION
                };
                self.last_frame_time = Some(now);

                // Accumulate time for fixed timestep simulation
                self.accumulated_time += delta_time;

                // Run simulation ticks (fixed timestep)
                while self.accumulated_time >= Self::TICK_DURATION {
                    if let Some(sim) = &mut self.simulation {
                        // TODO: Get real input
                        let inputs = vec![PlayerInput::default()];
                        sim.tick(&inputs);
                    }
                    self.accumulated_time -= Self::TICK_DURATION;
                }

                // Render
                let render_result = self.render_frame(delta_time);
                match render_result {
                    Ok(_) => {}
                    Err(wgpu::SurfaceError::Lost | wgpu::SurfaceError::Outdated) => {
                        if let (Some(renderer), Some(window)) = (&mut self.renderer, &self.window) {
                            renderer.resize(window.inner_size());
                        }
                    }
                    Err(e) => {
                        tracing::error!("Render error: {e:?}, exiting");
                        event_loop.exit();
                    }
                }

                // Request another frame
                if let Some(window) = &self.window {
                    window.request_redraw();
                }
            }

            WindowEvent::KeyboardInput { event, .. } => {
                tracing::trace!("Key event: {:?}", event);
                // TODO: Feed to input system
            }

            _ => {}
        }
    }
}
