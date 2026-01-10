//! Astranyx Client
//!
//! Game client supporting both WASM (browser) and native platforms.

pub mod game;
pub mod hud;
pub mod renderer;

use std::time::Instant;

use glam::Vec4;
use three_d::*;

use astranyx_core::input::PlayerInput;
use astranyx_core::simulation::{Simulation, SimulationConfig};

use crate::game::{colors, mesh_names};
use crate::renderer::{meshes, GameRenderer, MeshBuilder};

/// Simple input state tracker using three-d's Key enum.
#[derive(Default)]
struct InputState {
    up: bool,
    down: bool,
    left: bool,
    right: bool,
    fire: bool,
    special: bool,
    focus: bool,
}

impl InputState {
    fn to_player_input(&self) -> PlayerInput {
        let mut input = PlayerInput::new();
        if self.up { input.set(PlayerInput::UP, true); }
        if self.down { input.set(PlayerInput::DOWN, true); }
        if self.left { input.set(PlayerInput::LEFT, true); }
        if self.right { input.set(PlayerInput::RIGHT, true); }
        if self.fire { input.set(PlayerInput::FIRE, true); }
        if self.special { input.set(PlayerInput::SPECIAL, true); }
        if self.focus { input.set(PlayerInput::FOCUS, true); }
        input
    }

    fn handle_key(&mut self, key: Key, pressed: bool) {
        match key {
            Key::W | Key::ArrowUp => self.up = pressed,
            Key::S | Key::ArrowDown => self.down = pressed,
            Key::A | Key::ArrowLeft => self.left = pressed,
            Key::D | Key::ArrowRight => self.right = pressed,
            Key::Space | Key::Z => self.fire = pressed,
            Key::X => self.special = pressed,
            Key::C => self.focus = pressed,
            _ => {}
        }
    }
}

/// Run the game (native entry point).
#[cfg(feature = "native")]
pub fn run() -> anyhow::Result<()> {
    use tracing_subscriber::{fmt, prelude::*, EnvFilter};

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env().add_directive("astranyx=debug".parse()?))
        .init();

    tracing::info!("Starting Astranyx (native)");

    // Create window and context
    let window = Window::new(WindowSettings {
        title: "Astranyx".to_string(),
        max_size: Some((1920, 1080)),
        ..Default::default()
    })?;

    let context = window.gl();

    // Initialize game renderer and register meshes
    let mut game_renderer = GameRenderer::new();
    register_all_meshes(&mut game_renderer);

    // Initialize simulation
    let config = SimulationConfig::default();
    let mut simulation = Simulation::new(config, 12345, 1);
    simulation.load_embedded_scripts();
    tracing::info!(
        "Loaded {} enemy scripts",
        simulation.scripts.loaded_enemy_types().len()
    );

    // Set up camera - perspective for now (easier to debug)
    let mut camera = Camera::new_perspective(
        window.viewport(),
        vec3(960.0, 540.0, 1000.0), // position - further back
        vec3(960.0, 540.0, 0.0),    // target
        vec3(0.0, 1.0, 0.0),        // up
        degrees(60.0),              // field of view
        0.1,
        10000.0,
    );

    // Create lights
    let ambient = AmbientLight::new(&context, 0.4, Srgba::WHITE);
    let directional = DirectionalLight::new(&context, 2.0, Srgba::WHITE, vec3(-1.0, -1.0, -1.0));

    // Input state
    let mut input_state = InputState::default();

    // Timing
    let mut last_frame = Instant::now();
    let mut accumulated_time = 0.0f32;
    const TICK_DURATION: f32 = 1.0 / 30.0;

    // Main loop
    window.render_loop(move |mut frame_input| {
        // Handle input
        for event in frame_input.events.iter() {
            match event {
                Event::KeyPress { kind, .. } => {
                    input_state.handle_key(*kind, true);
                }
                Event::KeyRelease { kind, .. } => {
                    input_state.handle_key(*kind, false);
                }
                _ => {}
            }
        }

        // Timing
        let now = Instant::now();
        let delta = now.duration_since(last_frame).as_secs_f32();
        last_frame = now;
        game_renderer.update_time(delta);

        // Fixed timestep simulation
        accumulated_time += delta;
        while accumulated_time >= TICK_DURATION {
            let inputs = vec![input_state.to_player_input()];
            simulation.tick(&inputs);
            accumulated_time -= TICK_DURATION;
        }

        // Update camera viewport
        camera.set_viewport(frame_input.viewport);

        // Clear screen
        frame_input
            .screen()
            .clear(ClearState::color_and_depth(0.02, 0.02, 0.06, 1.0, 1.0));

        // Render all entities
        render_game_state(
            &context,
            &game_renderer,
            &simulation.state,
            &camera,
            &[&ambient as &dyn Light, &directional as &dyn Light],
            &mut frame_input,
        );

        FrameOutput::default()
    });

    Ok(())
}

/// Register all game meshes with the renderer.
fn register_all_meshes(renderer: &mut GameRenderer) {
    use mesh_names::*;

    renderer.register_mesh(PLAYER_SHIP, &meshes::create_player_ship_mesh());
    renderer.register_mesh(ENEMY_BASIC, &meshes::create_enemy_ship_mesh());
    renderer.register_mesh(ENEMY_FAST, &meshes::create_drone_mesh());
    renderer.register_mesh(ENEMY_HEAVY, &meshes::create_tank_mesh());
    renderer.register_mesh(ENEMY_BOSS, &meshes::create_boss_core_mesh());
    renderer.register_mesh(BULLET_PLAYER, &meshes::create_bullet_mesh());
    renderer.register_mesh(BULLET_ENEMY, &meshes::create_bullet_mesh());
    renderer.register_mesh(MISSILE, &meshes::create_bullet_mesh());
    renderer.register_mesh(LASER, &meshes::create_laser_mesh());
    renderer.register_mesh(POWERUP_HEALTH, &meshes::create_powerup_mesh());
    renderer.register_mesh(POWERUP_WEAPON, &meshes::create_powerup_mesh());
    renderer.register_mesh(POWERUP_SPECIAL, &meshes::create_powerup_mesh());
    renderer.register_mesh(POWERUP_SHIELD, &meshes::create_powerup_mesh());
    renderer.register_mesh(POWERUP_SPEED, &meshes::create_powerup_mesh());

    let mut builder = MeshBuilder::new();
    builder.add_box(1.0, 1.0, 1.0);
    renderer.register_mesh("test_box", &builder.finish());

    tracing::info!("Registered all game meshes");
}

/// Render the game state.
fn render_game_state(
    context: &Context,
    game_renderer: &GameRenderer,
    state: &astranyx_core::simulation::GameState,
    camera: &Camera,
    lights: &[&dyn Light],
    frame_input: &mut FrameInput,
) {
    let time = game_renderer.time();

    // Render players
    for player in &state.players {
        if !player.is_alive() {
            continue;
        }

        let color = if player.is_invincible() {
            let blink = if (time * 10.0).sin() > 0.0 { 1.0 } else { 0.5 };
            Srgba::new(255, 255, 255, (blink * 200.0) as u8)
        } else {
            vec4_to_srgba(colors::PLAYER)
        };

        render_mesh(
            context,
            game_renderer,
            mesh_names::PLAYER_SHIP,
            vec3(player.position.x, player.position.y, 0.0),
            vec3(30.0, 30.0, 30.0),
            color,
            camera,
            lights,
            frame_input,
        );
    }

    // Render enemies
    for enemy in &state.enemies {
        if !enemy.is_alive() {
            continue;
        }

        let (mesh_name, color, scale) = game::get_enemy_render_info(enemy);
        render_mesh(
            context,
            game_renderer,
            mesh_name,
            vec3(enemy.position.x, enemy.position.y, 0.0),
            vec3(scale, scale, scale),
            vec4_to_srgba(color),
            camera,
            lights,
            frame_input,
        );
    }

    // Render projectiles
    for proj in &state.projectiles {
        let (mesh_name, color, scale) = game::get_projectile_render_info(proj);
        render_mesh(
            context,
            game_renderer,
            mesh_name,
            vec3(proj.position.x, proj.position.y, 0.0),
            vec3(scale, scale, scale),
            vec4_to_srgba(color),
            camera,
            lights,
            frame_input,
        );
    }

    // Render power-ups
    for power_up in &state.power_ups {
        let (mesh_name, color) = game::get_powerup_render_info(power_up);
        let pulse = 1.0 + (time * 3.0).sin() * 0.1;
        let scale = 20.0 * pulse;
        render_mesh(
            context,
            game_renderer,
            mesh_name,
            vec3(power_up.position.x, power_up.position.y, 0.0),
            vec3(scale, scale, scale),
            vec4_to_srgba(color),
            camera,
            lights,
            frame_input,
        );
    }
}

/// Render a single mesh instance.
fn render_mesh(
    context: &Context,
    game_renderer: &GameRenderer,
    mesh_name: &str,
    position: Vector3<f32>,
    scale: Vector3<f32>,
    color: Srgba,
    camera: &Camera,
    lights: &[&dyn Light],
    frame_input: &mut FrameInput,
) {
    let Some(cpu_mesh) = game_renderer.get_mesh(mesh_name) else {
        return;
    };

    let mut gm = Gm::new(
        Mesh::new(context, cpu_mesh),
        PhysicalMaterial::new_opaque(
            context,
            &CpuMaterial {
                albedo: color,
                ..Default::default()
            },
        ),
    );

    gm.set_transformation(
        Mat4::from_translation(position) * Mat4::from_nonuniform_scale(scale.x, scale.y, scale.z),
    );

    frame_input.screen().render(camera, &gm, lights);
}

/// Convert glam Vec4 color to three-d Srgba.
fn vec4_to_srgba(color: Vec4) -> Srgba {
    Srgba::new(
        (color.x * 255.0) as u8,
        (color.y * 255.0) as u8,
        (color.z * 255.0) as u8,
        (color.w * 255.0) as u8,
    )
}

/// WASM entry point - called from JavaScript.
#[cfg(feature = "wasm")]
#[wasm_bindgen::prelude::wasm_bindgen(start)]
pub async fn wasm_start() {
    console_error_panic_hook::set_once();
    tracing_wasm::set_as_global_default();

    tracing::info!("Starting Astranyx (WASM)");

    // TODO: WASM implementation with three-d
}
