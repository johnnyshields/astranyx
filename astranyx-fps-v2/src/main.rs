//! Astranyx FPS - Main Entry Point
//!
//! A Quake-style FPS with deterministic physics for lockstep multiplayer.

use std::collections::HashSet;

use astranyx_game::{PlayerInput, Simulation};
use astranyx_physics::MovementConfig;
use astranyx_renderer::camera::FirstPersonCamera;
use glam::Vec3;
use three_d::*;

/// Input state tracking
struct InputState {
    forward: bool,
    backward: bool,
    left: bool,
    right: bool,
    jump: bool,
    crouch: bool,
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
            crouch: false,
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
                crouch: self.crouch,
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
            Key::C => self.crouch = pressed,
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

    // Create simple level geometry for rendering
    let mut floor = Gm::new(
        Mesh::new(&context, &CpuMesh::square()),
        ColorMaterial {
            color: Srgba::new(80, 80, 85, 255),
            ..Default::default()
        },
    );
    floor.set_transformation(
        Mat4::from_translation(vec3(0.0, 0.0, 0.0))
            * Mat4::from_scale(100.0)
            * Mat4::from_angle_x(degrees(-90.0)),
    );

    // Walls
    let wall_material = ColorMaterial {
        color: Srgba::new(60, 55, 65, 255),
        ..Default::default()
    };

    let mut walls: Vec<Gm<Mesh, ColorMaterial>> = Vec::new();

    // North wall
    let mut wall_n = Gm::new(
        Mesh::new(&context, &CpuMesh::square()),
        wall_material.clone(),
    );
    wall_n.set_transformation(
        Mat4::from_translation(vec3(0.0, 2.5, -50.0)) * Mat4::from_scale(50.0),
    );
    walls.push(wall_n);

    // South wall
    let mut wall_s = Gm::new(
        Mesh::new(&context, &CpuMesh::square()),
        wall_material.clone(),
    );
    wall_s.set_transformation(
        Mat4::from_translation(vec3(0.0, 2.5, 50.0))
            * Mat4::from_angle_y(degrees(180.0))
            * Mat4::from_scale(50.0),
    );
    walls.push(wall_s);

    // East wall
    let mut wall_e = Gm::new(
        Mesh::new(&context, &CpuMesh::square()),
        wall_material.clone(),
    );
    wall_e.set_transformation(
        Mat4::from_translation(vec3(50.0, 2.5, 0.0))
            * Mat4::from_angle_y(degrees(-90.0))
            * Mat4::from_scale(50.0),
    );
    walls.push(wall_e);

    // West wall
    let mut wall_w = Gm::new(
        Mesh::new(&context, &CpuMesh::square()),
        wall_material.clone(),
    );
    wall_w.set_transformation(
        Mat4::from_translation(vec3(-50.0, 2.5, 0.0))
            * Mat4::from_angle_y(degrees(90.0))
            * Mat4::from_scale(50.0),
    );
    walls.push(wall_w);

    // Central pillar
    let mut pillar = Gm::new(
        Mesh::new(&context, &CpuMesh::cube()),
        ColorMaterial {
            color: Srgba::new(70, 65, 75, 255),
            ..Default::default()
        },
    );
    pillar.set_transformation(Mat4::from_translation(vec3(0.0, 2.0, 0.0)) * Mat4::from_scale(2.0));

    // Ambient light
    let ambient = AmbientLight::new(&context, 0.3, Srgba::WHITE);

    // Point light
    let light = PointLight::new(&context, 2.0, Srgba::WHITE, vec3(0.0, 10.0, 0.0), Attenuation::default());

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

        // Clear mouse delta after processing
        input_state.clear_mouse_delta();

        // Update camera from player state
        if let Some(player) = simulation.get_player(player_id) {
            let eye_pos = player.eye_position(&movement_config);
            fps_camera.position = eye_pos;
            fps_camera.angles = player.movement.view_angles;
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

        // Render
        frame_input
            .screen()
            .clear(ClearState::color_and_depth(0.1, 0.1, 0.15, 1.0, 1.0))
            .render(&camera, &[&floor], &[&ambient, &light])
            .render(&camera, walls.iter().collect::<Vec<_>>().as_slice(), &[&ambient, &light])
            .render(&camera, &[&pillar], &[&ambient, &light]);

        // Draw HUD
        if let Some(player) = simulation.get_player(player_id) {
            // Could add text overlay here for health, position, etc.
        }

        FrameOutput::default()
    });
}
