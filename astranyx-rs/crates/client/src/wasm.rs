//! WASM-specific initialization and event loop.

use std::sync::Arc;

use wasm_bindgen::prelude::*;
use winit::{
    dpi::PhysicalSize,
    event_loop::EventLoop,
    platform::web::WindowExtWebSys,
    window::Window,
};

use crate::app::App;

/// Run the game in WASM environment.
pub async fn run_wasm() -> anyhow::Result<()> {
    let event_loop = EventLoop::new()?;
    let mut app = App::new();

    // Run the event loop
    event_loop.run_app(&mut app)?;

    Ok(())
}

/// Attach the canvas to the DOM.
/// Called after window creation in WASM builds.
pub fn attach_canvas(window: &Window) -> Result<(), JsValue> {
    let web_window = web_sys::window().ok_or("no window")?;
    let document = web_window.document().ok_or("no document")?;
    let body = document.body().ok_or("no body")?;

    let canvas = window.canvas().ok_or("no canvas")?;
    canvas.set_id("astranyx-canvas");
    canvas.style().set_property("width", "100%")?;
    canvas.style().set_property("height", "100%")?;

    body.append_child(&canvas)?;

    Ok(())
}

/// Get the current timestamp in milliseconds (for frame timing).
pub fn now_ms() -> f64 {
    web_sys::window()
        .and_then(|w| w.performance())
        .map(|p| p.now())
        .unwrap_or(0.0)
}
