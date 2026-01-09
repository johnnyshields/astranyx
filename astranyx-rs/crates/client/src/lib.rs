//! Astranyx Client
//!
//! Game client supporting both WASM (browser) and native platforms.

pub mod app;
pub mod game;
pub mod hud;
pub mod input;
pub mod renderer;

#[cfg(feature = "wasm")]
pub mod wasm;

/// Run the game (native entry point).
#[cfg(feature = "native")]
pub fn run() -> anyhow::Result<()> {
    use tracing_subscriber::{fmt, prelude::*, EnvFilter};
    use winit::event_loop::EventLoop;
    use app::App;

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env().add_directive("astranyx=debug".parse()?))
        .init();

    tracing::info!("Starting Astranyx (native)");

    let event_loop = EventLoop::new()?;
    let mut app = App::new();

    event_loop.run_app(&mut app)?;

    Ok(())
}

/// WASM entry point - called from JavaScript.
#[cfg(feature = "wasm")]
#[wasm_bindgen::prelude::wasm_bindgen(start)]
pub async fn wasm_start() {
    console_error_panic_hook::set_once();
    tracing_wasm::set_as_global_default();

    tracing::info!("Starting Astranyx (WASM)");

    if let Err(e) = wasm::run_wasm().await {
        tracing::error!("Fatal error: {e}");
    }
}
