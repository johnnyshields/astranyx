//! Astranyx Client
//!
//! Game client supporting both WASM (browser) and native platforms.

pub mod effects;
pub mod game;
pub mod hud;
pub mod renderer;

use std::time::Instant;

use glam::Vec4;
use three_d::*;

use astranyx_core::entities::EntityId;
use astranyx_core::input::PlayerInput;
use astranyx_core::level::{CameraConfig, CameraProjection, CameraState, GameMode, GeometryDef, SegmentConfig};
use astranyx_core::path::PathSet;
use astranyx_core::simulation::{GameState, Simulation, SimulationConfig};

use crate::effects::{EffectEvent, VisualEffects};
use crate::game::{colors, mesh_names};
use crate::renderer::{meshes, GameRenderer, MeshBuilder};

/// Debug mode flag - enables shortcuts like Tab to skip segments.
const DEBUG_MODE: bool = true;

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
    debug_skip: bool,
    // Mouse movement for FPS modes
    mouse_dx: f32,
    mouse_dy: f32,
}

impl InputState {
    /// Convert to PlayerInput for shmup modes (2D movement).
    fn to_player_input_shmup(&self) -> PlayerInput {
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

    /// Convert to PlayerInput for FPS modes (3D movement + mouse aim).
    fn to_player_input_fps(&self, mouse_dx: f32, mouse_dy: f32) -> PlayerInput {
        let mut input = PlayerInput::new();
        // WASD for movement
        if self.up { input.set(PlayerInput::FORWARD, true); }
        if self.down { input.set(PlayerInput::BACKWARD, true); }
        if self.left { input.set(PlayerInput::LEFT, true); }
        if self.right { input.set(PlayerInput::RIGHT, true); }
        if self.fire { input.set(PlayerInput::FIRE, true); }
        if self.special { input.set(PlayerInput::SPECIAL, true); }
        // Mouse aiming
        input.set_mouse_delta(mouse_dx, mouse_dy);
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
            Key::Tab => self.debug_skip = pressed,
            _ => {}
        }
    }

    /// Check and consume the debug skip flag (returns true once per press).
    fn consume_debug_skip(&mut self) -> bool {
        if self.debug_skip {
            self.debug_skip = false;
            true
        } else {
            false
        }
    }

    /// Add mouse movement delta.
    fn add_mouse_delta(&mut self, dx: f32, dy: f32) {
        self.mouse_dx += dx;
        self.mouse_dy += dy;
    }

    /// Consume and reset mouse delta.
    fn consume_mouse_delta(&mut self) -> (f32, f32) {
        let delta = (self.mouse_dx, self.mouse_dy);
        self.mouse_dx = 0.0;
        self.mouse_dy = 0.0;
        delta
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
    simulation.init_level_from_scripts();

    tracing::info!(
        "Loaded {} enemy scripts, {} segments. Starting world: {}, segment: {}",
        simulation.scripts.loaded_enemy_types().len(),
        simulation.scripts.loaded_segment_ids().len(),
        simulation.state.level.world_id,
        simulation.state.level.segment_id
    );

    // Get initial camera config from segment
    let camera_config = simulation.scripts.get_segment_config(&simulation.state.level.segment_id)
        .map(|s| s.camera)
        .unwrap_or_default();
    let mut camera_state = CameraState::default();
    camera_state.position = camera_config.position;
    camera_state.target = camera_config.target;

    // Set up camera from segment config
    let mut camera = create_camera_from_config(&window.viewport(), &camera_config, &camera_state);

    // Create lights
    let ambient = AmbientLight::new(&context, 0.4, Srgba::WHITE);
    let directional = DirectionalLight::new(&context, 2.0, Srgba::WHITE, vec3(-1.0, -1.0, -1.0));

    // Visual effects (client-side only, uses Rapier)
    let mut visual_effects = VisualEffects::new();

    // Input state
    let mut input_state = InputState::default();

    // Timing
    let mut last_frame = Instant::now();
    let mut accumulated_time = 0.0f32;
    const TICK_DURATION: f32 = 1.0 / 30.0;

    // Track current segment for camera updates and geometry
    let mut current_segment_id = simulation.state.level.segment_id.clone();
    let mut camera_config = camera_config;
    let mut segment_config: Option<SegmentConfig> = simulation.scripts.get_segment_config(&current_segment_id);


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
                Event::MouseMotion { delta, .. } => {
                    input_state.add_mouse_delta(delta.0 as f32, delta.1 as f32);
                }
                _ => {}
            }
        }

        // Debug: Tab to skip to next segment
        if DEBUG_MODE && input_state.consume_debug_skip() {
            if let Some(next_segment) = simulation.debug_skip_to_next_segment() {
                tracing::info!("[DEBUG] Skipping to segment: {}", next_segment);
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
            // Track segment before tick to detect transitions
            let segment_before = simulation.state.level.segment_id.clone();
            let was_transitioning = simulation.state.level.transition.is_some();

            // Snapshot enemy positions before tick (for death detection)
            let enemies_before: std::collections::HashMap<EntityId, (glam::Vec2, glam::Vec2)> =
                simulation.state.enemies.iter()
                    .filter(|e| e.is_alive())
                    .map(|e| (e.id, (e.position, e.velocity)))
                    .collect();

            // Create input based on game mode
            let mode = &simulation.state.level.mode;
            let (mouse_dx, mouse_dy) = input_state.consume_mouse_delta();
            let player_input = if mode.is_first_person() {
                input_state.to_player_input_fps(mouse_dx, mouse_dy)
            } else {
                input_state.to_player_input_shmup()
            };
            let inputs = vec![player_input];
            simulation.tick(&inputs);

            // Detect enemy deaths and spawn effects
            // Skip if: transitioning, was transitioning, or segment just changed
            let segment_changed = simulation.state.level.segment_id != segment_before;
            let is_transitioning = simulation.state.level.transition.is_some();
            if !is_transitioning && !was_transitioning && !segment_changed {
                let current_ids: std::collections::HashSet<EntityId> =
                    simulation.state.enemies.iter()
                        .filter(|e| e.is_alive())
                        .map(|e| e.id)
                        .collect();

                for (id, (pos, vel)) in &enemies_before {
                    if !current_ids.contains(id) {
                        // Enemy died - spawn death effect
                        visual_effects.spawn_effect(EffectEvent::EnemyDeath {
                            position: glam::Vec3::new(pos.x, pos.y, 0.0),
                            velocity: glam::Vec3::new(vel.x, vel.y, 0.0),
                            size: 20.0,
                        });
                    }
                }
            }
            accumulated_time -= TICK_DURATION;
        }

        // Update visual effects physics
        visual_effects.update(delta);

        // Check for segment change and update camera config + geometry
        if simulation.state.level.segment_id != current_segment_id {
            current_segment_id = simulation.state.level.segment_id.clone();
            segment_config = simulation.scripts.get_segment_config(&current_segment_id);
            if let Some(ref config) = segment_config {
                camera_config = config.camera.clone();
                // Reset camera state for the new segment
                camera_state = CameraState::default();
                camera_state.position = camera_config.position;
                camera_state.target = camera_config.target;
                tracing::info!("Segment changed to: {} (mode: {:?}, geometry: {} objects)",
                    current_segment_id, config.mode, config.geometry.len());
            }
        }

        // Update camera state based on game mode
        update_camera_state_for_mode(&mut camera_state, &camera_config, &simulation.state, &simulation.paths);

        // Update camera from state
        camera = create_camera_from_config(&frame_input.viewport, &camera_config, &camera_state);

        // Clear screen
        frame_input
            .screen()
            .clear(ClearState::color_and_depth(0.02, 0.02, 0.06, 1.0, 1.0));

        // Render segment geometry (level visuals)
        if let Some(ref config) = segment_config {
            render_segment_geometry(
                &context,
                &config.geometry,
                &camera,
                &[&ambient as &dyn Light, &directional as &dyn Light],
                &mut frame_input,
            );
        }

        // Render all entities
        render_game_state(
            &context,
            &game_renderer,
            &simulation.state,
            &camera,
            &[&ambient as &dyn Light, &directional as &dyn Light],
            &mut frame_input,
        );

        // Render visual effects (debris)
        render_effects(
            &context,
            &visual_effects,
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

/// Global scale multiplier for all entities.
const RENDER_SCALE: f32 = 5.0;

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
    let mode = &state.level.mode;

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

        // Use effective position based on game mode
        let pos = player.effective_position(mode);
        let s = 30.0 * RENDER_SCALE;

        // Don't render player ship in first-person mode (you can't see yourself)
        if !mode.is_first_person() {
            render_mesh(
                context,
                game_renderer,
                mesh_names::PLAYER_SHIP,
                vec3(pos.x, pos.y, pos.z),
                vec3(s, s, s),
                color,
                camera,
                lights,
                frame_input,
            );
        }
    }

    // Render enemies (currently only 2D)
    for enemy in &state.enemies {
        if !enemy.is_alive() {
            continue;
        }

        let (mesh_name, color, base_scale) = game::get_enemy_render_info(enemy);
        let s = base_scale * RENDER_SCALE;
        render_mesh(
            context,
            game_renderer,
            mesh_name,
            vec3(enemy.position.x, enemy.position.y, 0.0),
            vec3(s, s, s),
            vec4_to_srgba(color),
            camera,
            lights,
            frame_input,
        );
    }

    // Render projectiles (currently only 2D)
    for proj in &state.projectiles {
        let (mesh_name, color, base_scale) = game::get_projectile_render_info(proj);
        let s = base_scale * RENDER_SCALE;
        render_mesh(
            context,
            game_renderer,
            mesh_name,
            vec3(proj.position.x, proj.position.y, 0.0),
            vec3(s, s, s),
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
        let s = 20.0 * RENDER_SCALE * pulse;
        render_mesh(
            context,
            game_renderer,
            mesh_name,
            vec3(power_up.position.x, power_up.position.y, 0.0),
            vec3(s, s, s),
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

/// Render visual effects (debris particles).
fn render_effects(
    context: &Context,
    effects: &VisualEffects,
    camera: &Camera,
    lights: &[&dyn Light],
    frame_input: &mut FrameInput,
) {
    for debris in effects.get_debris() {
        // Create a small cube for debris
        let cpu_mesh = CpuMesh::cube();

        let color = Srgba::new(
            (debris.color[0] * 255.0) as u8,
            (debris.color[1] * 255.0) as u8,
            (debris.color[2] * 255.0) as u8,
            (debris.color[3] * 255.0) as u8,
        );

        let mut gm = Gm::new(
            Mesh::new(context, &cpu_mesh),
            PhysicalMaterial::new_opaque(
                context,
                &CpuMaterial {
                    albedo: color,
                    ..Default::default()
                },
            ),
        );

        // Apply position, rotation, and scale
        let pos = debris.position;
        let rot = glam::Quat::from_xyzw(
            debris.rotation[0],
            debris.rotation[1],
            debris.rotation[2],
            debris.rotation[3],
        );
        let rot_mat = glam::Mat4::from_quat(rot);
        let s = debris.size * RENDER_SCALE * 0.5;

        gm.set_transformation(
            Mat4::from_translation(vec3(pos.x, pos.y, pos.z))
                * Mat4::new(
                    rot_mat.x_axis.x, rot_mat.x_axis.y, rot_mat.x_axis.z, rot_mat.x_axis.w,
                    rot_mat.y_axis.x, rot_mat.y_axis.y, rot_mat.y_axis.z, rot_mat.y_axis.w,
                    rot_mat.z_axis.x, rot_mat.z_axis.y, rot_mat.z_axis.z, rot_mat.z_axis.w,
                    rot_mat.w_axis.x, rot_mat.w_axis.y, rot_mat.w_axis.z, rot_mat.w_axis.w,
                )
                * Mat4::from_nonuniform_scale(s, s, s),
        );

        frame_input.screen().render(camera, &gm, lights);
    }
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

/// Render segment geometry (placeholder boxes for level visuals).
fn render_segment_geometry(
    context: &Context,
    geometry: &[GeometryDef],
    camera: &Camera,
    lights: &[&dyn Light],
    frame_input: &mut FrameInput,
) {
    for geo in geometry {
        let color = Srgba::new(geo.color[0], geo.color[1], geo.color[2], 255);

        match geo.geo_type.as_str() {
            "box" => {
                let cpu_mesh = CpuMesh::cube();

                let mut gm = Gm::new(
                    Mesh::new(context, &cpu_mesh),
                    PhysicalMaterial::new_opaque(
                        context,
                        &CpuMaterial {
                            albedo: color,
                            ..Default::default()
                        },
                    ),
                );

                // Transform: position + scale
                // Note: Three-d cube is -0.5 to 0.5, so size directly maps to scale
                gm.set_transformation(
                    Mat4::from_translation(vec3(geo.position.x, geo.position.y, geo.position.z))
                        * Mat4::from_nonuniform_scale(geo.size.x, geo.size.y, geo.size.z),
                );

                frame_input.screen().render(camera, &gm, lights);
            }
            // Future: "cylinder", "plane", etc.
            _ => {}
        }
    }
}

/// Create a three-d Camera from a CameraConfig and CameraState.
fn create_camera_from_config(viewport: &Viewport, config: &CameraConfig, state: &CameraState) -> Camera {
    let pos = state.final_position();
    let target = state.target;

    match config.projection {
        CameraProjection::Perspective => Camera::new_perspective(
            *viewport,
            vec3(pos.x, pos.y, pos.z),
            vec3(target.x, target.y, target.z),
            vec3(0.0, 1.0, 0.0),
            degrees(config.fov),
            config.near,
            config.far,
        ),
        CameraProjection::Orthographic { scale } => Camera::new_orthographic(
            *viewport,
            vec3(pos.x, pos.y, pos.z),
            vec3(target.x, target.y, target.z),
            vec3(0.0, 1.0, 0.0),
            scale,
            config.near,
            config.far,
        ),
    }
}

/// Update camera state based on game mode, config, and game state.
fn update_camera_state_for_mode(
    state: &mut CameraState,
    config: &CameraConfig,
    game_state: &GameState,
    paths: &PathSet,
) {
    let mode = &game_state.level.mode;
    let player = game_state.players.first();

    match mode {
        GameMode::SideScroll { .. } => {
            // Classic shmup - fixed camera or slight player follow
            if config.follow_player {
                if let Some(player) = player.filter(|p| p.is_alive()) {
                    let target_pos = glam::Vec3::new(
                        player.position.x + config.follow_offset.x,
                        config.position.y,
                        config.position.z,
                    );
                    state.position = if config.smoothing > 0.0 {
                        state.position.lerp(target_pos, 1.0 - config.smoothing)
                    } else {
                        target_pos
                    };
                    state.target = glam::Vec3::new(state.position.x, state.position.y, 0.0);
                }
            } else {
                state.position = config.position;
                state.target = config.target;
            }
        }

        GameMode::OnRails { path_id } | GameMode::Turret { path_id } => {
            // Camera follows path
            if let Some(path) = paths.get(path_id) {
                let (path_pos, path_rot) = path.sample_at_frame(game_state.level.segment_frame);
                state.position = path_pos;

                // Calculate forward direction from rotation
                let forward = path_rot * glam::Vec3::NEG_Z;
                state.target = path_pos + forward * 100.0;
            } else {
                // Fallback to config if path not found
                state.position = config.position;
                state.target = config.target;
            }
        }

        GameMode::FreeFlight => {
            // Chase camera behind player
            if let Some(player) = player.filter(|p| p.is_alive()) {
                let forward = player.forward_3d();
                let offset = -forward * 200.0 + glam::Vec3::new(0.0, 50.0, 0.0);
                let target_pos = player.position_3d + offset;

                state.position = if config.smoothing > 0.0 {
                    state.position.lerp(target_pos, 1.0 - config.smoothing)
                } else {
                    target_pos
                };
                state.target = player.position_3d;
            } else {
                state.position = config.position;
                state.target = config.target;
            }
        }

        GameMode::FirstPerson => {
            // First-person camera at player eye height
            if let Some(player) = player.filter(|p| p.is_alive()) {
                let eye_height = 1.7;
                state.position = player.position_3d + glam::Vec3::new(0.0, eye_height, 0.0);
                let forward = player.forward_3d();
                state.target = state.position + forward * 100.0;
            } else {
                state.position = config.position;
                state.target = config.target;
            }
        }
    }
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
