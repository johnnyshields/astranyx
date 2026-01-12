//! Astranyx FPS - Main Entry Point
//!
//! A Quake-style FPS with deterministic physics for lockstep multiplayer.

use std::collections::HashSet;
use std::path::Path;

use astranyx_game::{PlayerInput, Simulation};
use astranyx_physics::movement::Stance;
use astranyx_physics::MovementConfig;
use astranyx_renderer::camera::FirstPersonCamera;
use glam::Vec3;
use image::GenericImageView;
use three_d::*;

// ============================================================================
// PBR Material Loading
// ============================================================================

/// A set of PBR textures for a material (with optional height map for parallax)
struct PbrTextures {
    albedo: CpuTexture,
    normal: CpuTexture,
    /// Combined metallic-roughness texture (glTF format: G=roughness, B=metallic)
    metallic_roughness: CpuTexture,
    ao: CpuTexture,
    /// Height map for parallax occlusion mapping (white = high, black = low)
    height: Option<CpuTexture>,
}

/// Load a PNG texture from disk
fn load_texture_from_file(path: &str) -> Option<CpuTexture> {
    let path = Path::new(path);
    if !path.exists() {
        eprintln!("Texture not found: {}", path.display());
        return None;
    }

    match image::open(path) {
        Ok(img) => {
            let (width, height) = img.dimensions();
            let rgba = img.to_rgba8();
            let pixels: Vec<[u8; 4]> = rgba.chunks_exact(4)
                .map(|c| [c[0], c[1], c[2], c[3]])
                .collect();

            Some(CpuTexture {
                name: path.file_name().unwrap_or_default().to_string_lossy().to_string(),
                data: TextureData::RgbaU8(pixels),
                width,
                height,
                min_filter: Interpolation::Linear,
                mag_filter: Interpolation::Linear,
                mipmap: None,
                wrap_s: Wrapping::Repeat,
                wrap_t: Wrapping::Repeat,
            })
        }
        Err(e) => {
            eprintln!("Failed to load texture {}: {}", path.display(), e);
            None
        }
    }
}

/// Combine separate metallic and roughness textures into glTF format
/// glTF stores: R=unused, G=roughness, B=metallic, A=unused
fn combine_metallic_roughness(
    metallic_path: &str,
    roughness_path: &str,
) -> Option<CpuTexture> {
    let roughness_img = image::open(roughness_path).ok()?;
    let metallic_img = image::open(metallic_path).ok();

    let (width, height) = roughness_img.dimensions();
    let roughness_rgba = roughness_img.to_rgba8();

    // If metallic texture exists, combine them; otherwise use roughness only
    let pixels: Vec<[u8; 4]> = if let Some(met_img) = metallic_img {
        let metallic_rgba = met_img.to_rgba8();
        roughness_rgba
            .chunks_exact(4)
            .zip(metallic_rgba.chunks_exact(4))
            .map(|(r, m)| {
                // glTF format: G=roughness (from R channel), B=metallic (from R channel)
                [0, r[0], m[0], 255]
            })
            .collect()
    } else {
        // No metallic - assume non-metallic (metallic = 0)
        roughness_rgba
            .chunks_exact(4)
            .map(|r| [0, r[0], 0, 255])
            .collect()
    };

    Some(CpuTexture {
        name: "metallic_roughness".to_string(),
        data: TextureData::RgbaU8(pixels),
        width,
        height,
        min_filter: Interpolation::Linear,
        mag_filter: Interpolation::Linear,
        mipmap: None,
        wrap_s: Wrapping::Repeat,
        wrap_t: Wrapping::Repeat,
    })
}

/// Load a PBR texture set from a directory
fn load_pbr_textures(base_path: &str, prefix: &str) -> PbrTextures {
    let load = |suffix: &str, default_name: &str| -> CpuTexture {
        let path = format!("{}/{}_{}", base_path, prefix, suffix);
        load_texture_from_file(&path).unwrap_or_else(|| create_default_texture(default_name))
    };

    // Combine metallic + roughness into glTF format
    let metallic_path = format!("{}/{}_{}", base_path, prefix, "metallic.png");
    let roughness_path = format!("{}/{}_{}", base_path, prefix, "roughness.png");
    let metallic_roughness = combine_metallic_roughness(&metallic_path, &roughness_path)
        .unwrap_or_else(|| create_default_texture("metallic_roughness"));

    PbrTextures {
        albedo: load("albedo.png", "albedo"),
        normal: load("normal-ogl.png", "normal"),
        metallic_roughness,
        ao: load("ao.png", "ao"),
        height: load_texture_from_file(&format!("{}/{}_{}", base_path, prefix, "height.png")),
    }
}

/// Create a default solid color texture as fallback
fn create_default_texture(name: &str) -> CpuTexture {
    let color: [u8; 4] = if name.contains("normal") {
        // Default normal map (pointing straight out)
        [128, 128, 255, 255]
    } else if name.contains("metallic_roughness") {
        // Default metallic-roughness (glTF: G=roughness=0.5, B=metallic=0)
        [0, 128, 0, 255]
    } else if name.contains("ao") {
        // Default AO (no occlusion)
        [255, 255, 255, 255]
    } else {
        // Default albedo (gray)
        [128, 128, 128, 255]
    };

    CpuTexture {
        name: name.to_string(),
        data: TextureData::RgbaU8(vec![color]),
        width: 1,
        height: 1,
        min_filter: Interpolation::Nearest,
        mag_filter: Interpolation::Nearest,
        mipmap: None,
        wrap_s: Wrapping::Repeat,
        wrap_t: Wrapping::Repeat,
    }
}

/// Create a PhysicalMaterial from PBR textures (with height map support for parallax)
fn create_pbr_material(context: &Context, textures: &PbrTextures) -> PhysicalMaterial {
    PhysicalMaterial {
        name: textures.albedo.name.clone(),
        albedo: Srgba::WHITE,
        albedo_texture: Some(Texture2DRef::from_cpu_texture(context, &textures.albedo)),
        metallic: 1.0, // Texture overrides this
        roughness: 1.0, // Texture overrides this
        metallic_roughness_texture: Some(Texture2DRef::from_cpu_texture(
            context,
            &textures.metallic_roughness,
        )),
        occlusion_strength: 1.0,
        occlusion_texture: Some(Texture2DRef::from_cpu_texture(context, &textures.ao)),
        normal_scale: 1.0,
        normal_texture: Some(Texture2DRef::from_cpu_texture(context, &textures.normal)),
        render_states: RenderStates::default(),
        is_transparent: false,
        emissive: Srgba::BLACK,
        emissive_texture: None,
        lighting_model: LightingModel::Cook(
            NormalDistributionFunction::TrowbridgeReitzGGX,
            GeometryFunction::SmithSchlickGGX,
        ),
        // Parallax occlusion mapping settings
        height_texture: textures
            .height
            .as_ref()
            .map(|h| Texture2DRef::from_cpu_texture(context, h)),
        height_scale: 0.08,
        height_max_layers: 16.0,
        height_iterations: 3,
    }
}

/// Create a square mesh with proper UVs for texture tiling
fn create_tiled_square(context: &Context, uv_scale: f32) -> Mesh {
    let mut mesh = CpuMesh::square();

    // Scale UVs for tiling (larger scale = more tiles)
    if let Some(ref mut uvs) = mesh.uvs {
        for uv in uvs.iter_mut() {
            uv.x *= uv_scale;
            uv.y *= uv_scale;
        }
    }

    Mesh::new(context, &mesh)
}

/// Input state tracking
struct InputState {
    forward: bool,
    backward: bool,
    left: bool,
    right: bool,
    jump: bool,
    crouch_pressed: bool,
    prone_pressed: bool,
    sprint: bool,
    fire: bool,
    mouse_delta: (f32, f32),
    keys_pressed: HashSet<Key>,
}

impl Default for InputState {
    fn default() -> Self {
        Self {
            forward: false,
            backward: false,
            left: false,
            right: false,
            jump: false,
            crouch_pressed: false,
            prone_pressed: false,
            sprint: false,
            fire: false,
            mouse_delta: (0.0, 0.0),
            keys_pressed: HashSet::new(),
        }
    }
}

impl InputState {
    fn to_player_input(&self) -> PlayerInput {
        PlayerInput {
            movement: astranyx_game::input::MovementInput {
                forward: self.forward,
                backward: self.backward,
                left: self.left,
                right: self.right,
            },
            mouse_delta: self.mouse_delta,
            actions: astranyx_game::input::ActionInput {
                fire: self.fire,
                aim: false,
                jump: self.jump,
                // Pass raw button states - StanceState handles edge detection
                crouch: self.crouch_pressed,
                prone: self.prone_pressed,
                sprint: self.sprint,
                use_item: false,
                reload: false,
            },
            frame: 0,
        }
    }

    fn handle_key(&mut self, key: Key, pressed: bool) {
        if pressed {
            self.keys_pressed.insert(key);
        } else {
            self.keys_pressed.remove(&key);
        }

        match key {
            Key::W => self.forward = pressed,
            Key::S => self.backward = pressed,
            Key::A => self.left = pressed,
            Key::D => self.right = pressed,
            Key::Space => self.jump = pressed,
            Key::C => self.crouch_pressed = pressed,
            Key::Z => self.prone_pressed = pressed,
            _ => {}
        }
    }

    fn handle_mouse_button(&mut self, button: MouseButton, pressed: bool) {
        if button == MouseButton::Left {
            self.fire = pressed;
        }
    }

    fn handle_mouse_motion(&mut self, delta: (f32, f32)) {
        self.mouse_delta = delta;
    }

    fn clear_mouse_delta(&mut self) {
        self.mouse_delta = (0.0, 0.0);
    }
}

fn main() {
    env_logger::init();

    // Create window
    let window = Window::new(WindowSettings {
        title: "Astranyx FPS v2".to_string(),
        max_size: Some((1920, 1080)),
        ..Default::default()
    })
    .unwrap();

    let context = window.gl();

    // Create simulation
    let mut simulation = Simulation::test();
    let player_id = simulation.add_player("Player1");

    // Movement config
    let movement_config = MovementConfig::default();

    // Create camera
    let mut fps_camera = FirstPersonCamera::new(Vec3::new(0.0, 1.6, 0.0));
    fps_camera.fov = 90.0;

    // Input state
    let mut input_state = InputState::default();
    let mut mouse_captured = false;

    // ========================================================================
    // Load PBR Textures
    // ========================================================================
    println!("Loading textures...");

    // Load brick textures for walls
    let brick_textures = load_pbr_textures(
        "assets/textures/brick/alley-brick-wall-bl",
        "alley-brick-wall",
    );
    let brick_material = create_pbr_material(&context, &brick_textures);

    // Load concrete textures for floor
    let concrete_textures = load_pbr_textures(
        "assets/textures/concrete/broken_down_concrete2_bl",
        "broken_down_concrete2",
    );
    let floor_material = create_pbr_material(&context, &concrete_textures);

    // Load metal textures for pillar
    let metal_textures = load_pbr_textures(
        "assets/textures/metal/abstract-alien-metal-bl",
        "abstract-alien-metal",
    );
    let metal_material = create_pbr_material(&context, &metal_textures);

    println!("Textures loaded!");

    // ========================================================================
    // Create Level Geometry with PBR Materials
    // ========================================================================

    // Floor - large tiled surface
    let floor_uv_scale = 20.0; // 20 tiles across
    let mut floor = Gm::new(
        create_tiled_square(&context, floor_uv_scale),
        floor_material,
    );
    floor.set_transformation(
        Mat4::from_translation(vec3(0.0, 0.0, 0.0))
            * Mat4::from_scale(100.0)
            * Mat4::from_angle_x(degrees(-90.0)),
    );

    // Walls with brick texture
    let wall_uv_scale = 10.0; // 10 brick tiles per wall
    let mut walls: Vec<Gm<Mesh, PhysicalMaterial>> = Vec::new();

    // North wall
    let mut wall_n = Gm::new(
        create_tiled_square(&context, wall_uv_scale),
        brick_material.clone(),
    );
    wall_n.set_transformation(
        Mat4::from_translation(vec3(0.0, 2.5, -50.0)) * Mat4::from_scale(50.0),
    );
    walls.push(wall_n);

    // South wall
    let mut wall_s = Gm::new(
        create_tiled_square(&context, wall_uv_scale),
        brick_material.clone(),
    );
    wall_s.set_transformation(
        Mat4::from_translation(vec3(0.0, 2.5, 50.0))
            * Mat4::from_angle_y(degrees(180.0))
            * Mat4::from_scale(50.0),
    );
    walls.push(wall_s);

    // East wall
    let mut wall_e = Gm::new(
        create_tiled_square(&context, wall_uv_scale),
        brick_material.clone(),
    );
    wall_e.set_transformation(
        Mat4::from_translation(vec3(50.0, 2.5, 0.0))
            * Mat4::from_angle_y(degrees(-90.0))
            * Mat4::from_scale(50.0),
    );
    walls.push(wall_e);

    // West wall
    let mut wall_w = Gm::new(
        create_tiled_square(&context, wall_uv_scale),
        brick_material.clone(),
    );
    wall_w.set_transformation(
        Mat4::from_translation(vec3(-50.0, 2.5, 0.0))
            * Mat4::from_angle_y(degrees(90.0))
            * Mat4::from_scale(50.0),
    );
    walls.push(wall_w);

    // Central pillar with metal texture
    let pillar_uv_scale = 2.0;
    let mut pillar_mesh = CpuMesh::cube();
    // Scale UVs for cube
    if let Some(ref mut uvs) = pillar_mesh.uvs {
        for uv in uvs.iter_mut() {
            uv.x *= pillar_uv_scale;
            uv.y *= pillar_uv_scale;
        }
    }
    let mut pillar = Gm::new(
        Mesh::new(&context, &pillar_mesh),
        metal_material,
    );
    pillar.set_transformation(Mat4::from_translation(vec3(0.0, 2.0, 0.0)) * Mat4::from_scale(2.0));

    // ========================================================================
    // Lighting Setup
    // ========================================================================

    // Ambient light - slightly warm tint
    let ambient = AmbientLight::new(&context, 0.15, Srgba::new(255, 250, 240, 255));

    // Main overhead point light - bright
    let light_main = PointLight::new(
        &context,
        3.0,
        Srgba::new(255, 250, 240, 255), // Warm white
        vec3(0.0, 8.0, 0.0),
        Attenuation {
            constant: 0.5,
            linear: 0.05,
            quadratic: 0.01,
        },
    );

    // Secondary fill lights for better visibility
    let light_fill1 = PointLight::new(
        &context,
        1.5,
        Srgba::new(200, 220, 255, 255), // Cool blue tint
        vec3(30.0, 5.0, 30.0),
        Attenuation {
            constant: 0.5,
            linear: 0.05,
            quadratic: 0.005,
        },
    );

    let light_fill2 = PointLight::new(
        &context,
        1.5,
        Srgba::new(255, 220, 200, 255), // Warm orange tint
        vec3(-30.0, 5.0, -30.0),
        Attenuation {
            constant: 0.5,
            linear: 0.05,
            quadratic: 0.005,
        },
    );

    // Main loop
    window.render_loop(move |mut frame_input| {
        // Handle input events
        for event in frame_input.events.iter() {
            match event {
                Event::KeyPress { kind, modifiers, handled } if !*handled => {
                    input_state.handle_key(*kind, true);
                    input_state.sprint = modifiers.shift;

                    // Toggle mouse capture with Escape
                    if *kind == Key::Escape {
                        mouse_captured = !mouse_captured;
                    }

                    // Quit with Q
                    if *kind == Key::Q {
                        return FrameOutput {
                            exit: true,
                            ..Default::default()
                        };
                    }
                }
                Event::KeyRelease { kind, modifiers, handled } if !*handled => {
                    input_state.handle_key(*kind, false);
                    input_state.sprint = modifiers.shift;
                }
                Event::MousePress { button, position, modifiers, handled } if !*handled => {
                    input_state.handle_mouse_button(*button, true);
                    if !mouse_captured {
                        mouse_captured = true;
                    }
                }
                Event::MouseRelease { button, position, modifiers, handled } if !*handled => {
                    input_state.handle_mouse_button(*button, false);
                }
                Event::MouseMotion { delta, .. } if mouse_captured => {
                    input_state.handle_mouse_motion(*delta);
                }
                _ => {}
            }
        }

        // Update simulation
        let player_input = input_state.to_player_input();
        simulation.tick(&[player_input]);

        // Clear frame-specific input after processing
        input_state.clear_mouse_delta();

        // Update camera from player state
        if let Some(player) = simulation.get_player(player_id) {
            let eye_pos = player.eye_position(&movement_config);
            fps_camera.position = eye_pos;
            fps_camera.angles = player.movement.view_angles;

            // Debug: print stance when it changes or every 60 frames
            static mut LAST_STANCE: Option<Stance> = None;
            static mut LAST_BASE: Option<Stance> = None;
            let stance_changed = unsafe {
                let changed = LAST_STANCE != Some(player.movement.stance.current_stance)
                    || LAST_BASE != Some(player.movement.stance.base_stance);
                LAST_STANCE = Some(player.movement.stance.current_stance);
                LAST_BASE = Some(player.movement.stance.base_stance);
                changed
            };

            if stance_changed || simulation.frame % 60 == 0 {
                println!(
                    "[{}] eye_y: {:.2} stance: {:?} (base: {:?}) C:{} Z:{} crouch_f: {:.2} prone_f: {:.2}",
                    simulation.frame,
                    eye_pos.y,
                    player.movement.stance.current_stance,
                    player.movement.stance.base_stance,
                    input_state.crouch_pressed,
                    input_state.prone_pressed,
                    player.movement.crouch_fraction,
                    player.movement.prone_fraction,
                );
            }
        }

        // Create three-d camera
        fps_camera.aspect = frame_input.viewport.aspect();
        let pos = fps_camera.position;
        let fwd = fps_camera.forward();
        let target = pos + fwd;
        let camera = Camera::new_perspective(
            frame_input.viewport,
            vec3(pos.x, pos.y, pos.z),
            vec3(target.x, target.y, target.z),
            vec3(0.0, 1.0, 0.0),
            degrees(fps_camera.fov),
            fps_camera.near,
            fps_camera.far,
        );

        // Render with PBR lighting
        let lights: [&dyn Light; 4] = [&ambient, &light_main, &light_fill1, &light_fill2];

        frame_input
            .screen()
            .clear(ClearState::color_and_depth(0.05, 0.05, 0.08, 1.0, 1.0))
            .render(&camera, &[&floor], &lights)
            .render(&camera, walls.iter().collect::<Vec<_>>().as_slice(), &lights)
            .render(&camera, &[&pillar], &lights);

        // Draw HUD
        if let Some(player) = simulation.get_player(player_id) {
            // Could add text overlay here for health, position, etc.
        }

        FrameOutput::default()
    });
}
