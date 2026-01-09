//! WASM-specific implementation.
//!
//! Uses a simpler architecture than native since WASM doesn't support
//! blocking on futures and has different event loop requirements.

use std::cell::RefCell;
use std::sync::Arc;

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use winit::{
    application::ApplicationHandler,
    event::WindowEvent,
    event_loop::{ActiveEventLoop, EventLoop},
    platform::web::WindowAttributesExtWebSys,
    window::{Window, WindowId},
};

use crate::renderer::Renderer;

/// Run the game in WASM environment.
pub async fn run_wasm() -> anyhow::Result<()> {
    let event_loop = EventLoop::new()?;
    let mut app = WasmApp::new();

    // Run event loop (this doesn't return on WASM)
    event_loop.run_app(&mut app)?;

    Ok(())
}

fn get_canvas() -> Option<web_sys::HtmlCanvasElement> {
    let window = web_sys::window()?;
    let document = window.document()?;
    let canvas = document.get_element_by_id("astranyx-canvas")?;
    let canvas: web_sys::HtmlCanvasElement = canvas.dyn_into().ok()?;

    // Set canvas size to match its display size
    let dpr = window.device_pixel_ratio();
    let rect = canvas.get_bounding_client_rect();
    let width = (rect.width() * dpr) as u32;
    let height = (rect.height() * dpr) as u32;

    canvas.set_width(width.max(1));
    canvas.set_height(height.max(1));

    tracing::info!("Canvas size: {}x{} (dpr: {})", width, height, dpr);

    Some(canvas)
}

/// WASM application state.
struct WasmApp {
    window: Option<Arc<Window>>,
    renderer: Option<Renderer>,
    renderer_initializing: bool,
}

impl WasmApp {
    fn new() -> Self {
        Self {
            window: None,
            renderer: None,
            renderer_initializing: false,
        }
    }
}

impl ApplicationHandler for WasmApp {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        if self.window.is_some() {
            return;
        }

        let canvas = match get_canvas() {
            Some(c) => c,
            None => {
                tracing::error!("Canvas not found");
                return;
            }
        };

        let window_attrs = Window::default_attributes()
            .with_title("Astranyx")
            .with_canvas(Some(canvas));

        let window = match event_loop.create_window(window_attrs) {
            Ok(w) => Arc::new(w),
            Err(e) => {
                tracing::error!("Failed to create window: {e}");
                return;
            }
        };

        self.window = Some(window.clone());
        self.renderer_initializing = true;

        // Initialize renderer asynchronously
        wasm_bindgen_futures::spawn_local(async move {
            match Renderer::new(window.clone()).await {
                Ok(renderer) => {
                    tracing::info!("Renderer created successfully");
                    // Store renderer in a global for the event loop to access
                    RENDERER.with(|r| {
                        *r.borrow_mut() = Some(renderer);
                    });
                    // Request initial redraw
                    window.request_redraw();
                }
                Err(e) => {
                    tracing::error!("Failed to create renderer: {e}");
                }
            }
        });

        tracing::info!("Window created, initializing renderer...");
    }

    fn window_event(&mut self, event_loop: &ActiveEventLoop, _id: WindowId, event: WindowEvent) {
        // Try to get renderer from global storage
        if self.renderer.is_none() {
            RENDERER.with(|r| {
                if let Some(mut renderer) = r.borrow_mut().take() {
                    // Resize to actual window size now that we have it
                    if let Some(window) = &self.window {
                        let size = window.inner_size();
                        if size.width > 0 && size.height > 0 {
                            tracing::info!("Initial resize to {:?}", size);
                            renderer.resize(size);
                        }
                    }
                    self.renderer = Some(renderer);
                    self.renderer_initializing = false;
                    tracing::info!("Renderer attached to app");
                }
            });
        }

        match event {
            WindowEvent::CloseRequested => {
                tracing::info!("Close requested");
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
                        Err(wgpu::SurfaceError::OutOfMemory | wgpu::SurfaceError::Timeout | wgpu::SurfaceError::Other) => {
                            tracing::error!("Fatal render error");
                        }
                    }
                }

                // Request next frame
                if let Some(window) = &self.window {
                    window.request_redraw();
                }
            }

            _ => {}
        }
    }
}

// Thread-local storage for renderer (WASM is single-threaded)
thread_local! {
    static RENDERER: RefCell<Option<Renderer>> = RefCell::new(None);
}
