//! Application state and event loop handler.

use std::sync::Arc;

use winit::{
    application::ApplicationHandler,
    dpi::PhysicalSize,
    event::WindowEvent,
    event_loop::ActiveEventLoop,
    window::{Window, WindowId},
};

use crate::renderer::Renderer;

/// Main application state.
pub struct App {
    window: Option<Arc<Window>>,
    renderer: Option<Renderer>,
}

impl App {
    pub fn new() -> Self {
        Self {
            window: None,
            renderer: None,
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
        let renderer = pollster::block_on(Renderer::new(window.clone()))
            .expect("failed to create renderer");

        self.window = Some(window);
        self.renderer = Some(renderer);

        tracing::info!("Window and renderer initialized");
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
                if let Some(renderer) = &mut self.renderer {
                    match renderer.render() {
                        Ok(_) => {}
                        Err(wgpu::SurfaceError::Lost | wgpu::SurfaceError::Outdated) => {
                            if let Some(window) = &self.window {
                                renderer.resize(window.inner_size());
                            }
                        }
                        Err(e) => {
                            tracing::error!("Render error: {e:?}, exiting");
                            event_loop.exit();
                        }
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
