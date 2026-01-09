//! WebGPU renderer for Astranyx.
//!
//! Uses wgpu for cross-platform GPU rendering (WebGPU on WASM, Vulkan/Metal/DX12 native).

pub mod camera;
pub mod mesh;
pub mod meshes;
mod phong_pipeline;
mod pipeline;
mod vertex;

use std::collections::HashMap;
use std::sync::Arc;

use glam::{Mat4, Vec3, Vec4};
use wgpu::{
    util::DeviceExt, Backends, BindGroup, Buffer, Device, DeviceDescriptor, Instance,
    InstanceDescriptor, PowerPreference, Queue, RequestAdapterOptions, Surface,
    SurfaceConfiguration, Texture, TextureUsages, TextureView,
};
use winit::{dpi::PhysicalSize, window::Window};

pub use camera::Camera;
pub use mesh::{MeshBuilder, MeshData, MeshVertex};
pub use phong_pipeline::{GlobalUniforms, InstanceUniforms, PhongPipeline};
pub use vertex::Vertex;

/// Cached GPU mesh with vertex buffer and bind group.
pub struct GpuMesh {
    pub vertex_buffer: Buffer,
    pub vertex_count: u32,
}

/// The main renderer.
pub struct Renderer {
    surface: Surface<'static>,
    device: Device,
    queue: Queue,
    config: SurfaceConfiguration,
    size: PhysicalSize<u32>,
    clear_color: wgpu::Color,

    // Pipelines
    phong_pipeline: PhongPipeline,
    #[allow(dead_code)]
    simple_pipeline: wgpu::RenderPipeline, // For backwards compat / simple shapes

    // Depth buffer
    depth_texture: Texture,
    depth_view: TextureView,

    // Camera
    camera: Camera,

    // Mesh cache
    mesh_cache: HashMap<String, GpuMesh>,

    // Per-frame instance data
    instance_buffer: Buffer,
    instance_bind_group: BindGroup,

    // Time tracking
    time: f32,

    // Legacy test triangle
    #[allow(dead_code)]
    vertex_buffer: Buffer,
    #[allow(dead_code)]
    num_vertices: u32,
}

impl Renderer {
    pub async fn new(window: Arc<Window>) -> anyhow::Result<Self> {
        let size = window.inner_size();
        tracing::info!("Initializing renderer with size: {:?}", size);

        // Create instance
        let instance = Instance::new(&InstanceDescriptor {
            backends: Backends::all(),
            ..Default::default()
        });

        // Create surface
        let surface = instance.create_surface(window)?;

        // Request adapter
        let adapter = instance
            .request_adapter(&RequestAdapterOptions {
                power_preference: PowerPreference::HighPerformance,
                compatible_surface: Some(&surface),
                force_fallback_adapter: false,
            })
            .await
            .ok_or_else(|| anyhow::anyhow!("No suitable GPU adapter found"))?;

        tracing::info!("Using adapter: {:?}", adapter.get_info());

        // Create device and queue
        // Use adapter limits for native, fall back to defaults for WASM
        let limits = if cfg!(target_arch = "wasm32") {
            wgpu::Limits::downlevel_webgl2_defaults()
        } else {
            wgpu::Limits::default()
        };

        let (device, queue) = adapter
            .request_device(
                &DeviceDescriptor {
                    label: Some("astranyx_device"),
                    required_features: wgpu::Features::empty(),
                    required_limits: limits,
                    memory_hints: Default::default(),
                },
                None,
            )
            .await
            .map_err(|e| anyhow::anyhow!("Failed to request device: {e}"))?;

        // Configure surface
        let surface_caps = surface.get_capabilities(&adapter);
        let surface_format = surface_caps
            .formats
            .iter()
            .find(|f| f.is_srgb())
            .copied()
            .unwrap_or(surface_caps.formats[0]);

        let config = SurfaceConfiguration {
            usage: TextureUsages::RENDER_ATTACHMENT,
            format: surface_format,
            width: size.width.max(1),
            height: size.height.max(1),
            present_mode: wgpu::PresentMode::AutoVsync,
            alpha_mode: surface_caps.alpha_modes[0],
            view_formats: vec![],
            desired_maximum_frame_latency: 2,
        };
        surface.configure(&device, &config);

        // Create depth buffer
        let (depth_texture, depth_view) =
            Self::create_depth_texture(&device, config.width, config.height);

        // Create pipelines
        let simple_pipeline = pipeline::create_render_pipeline(&device, surface_format);
        let phong_pipeline = PhongPipeline::new(&device, surface_format);

        // Create camera
        let mut camera = Camera::new();
        camera.set_aspect(config.width as f32 / config.height as f32);

        // Create instance buffer (for per-object uniforms)
        let instance_uniforms = InstanceUniforms::new(Mat4::IDENTITY, Vec4::ONE);
        let instance_buffer = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("instance_buffer"),
            contents: bytemuck::cast_slice(&[instance_uniforms]),
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        });
        let instance_bind_group = phong_pipeline.create_instance_bind_group(&device, &instance_buffer);

        // Create a test triangle (legacy)
        let vertices = &[
            Vertex {
                position: [0.0, 0.5, 0.0],
                color: [1.0, 0.0, 0.0],
            },
            Vertex {
                position: [-0.5, -0.5, 0.0],
                color: [0.0, 1.0, 0.0],
            },
            Vertex {
                position: [0.5, -0.5, 0.0],
                color: [0.0, 0.0, 1.0],
            },
        ];

        let vertex_buffer = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("vertex_buffer"),
            contents: bytemuck::cast_slice(vertices),
            usage: wgpu::BufferUsages::VERTEX,
        });

        Ok(Self {
            surface,
            device,
            queue,
            config,
            size,
            clear_color: wgpu::Color {
                r: 0.02,
                g: 0.02,
                b: 0.06,
                a: 1.0,
            },
            phong_pipeline,
            simple_pipeline,
            depth_texture,
            depth_view,
            camera,
            mesh_cache: HashMap::new(),
            instance_buffer,
            instance_bind_group,
            time: 0.0,
            vertex_buffer,
            num_vertices: vertices.len() as u32,
        })
    }

    fn create_depth_texture(device: &Device, width: u32, height: u32) -> (Texture, TextureView) {
        let texture = device.create_texture(&wgpu::TextureDescriptor {
            label: Some("depth_texture"),
            size: wgpu::Extent3d {
                width: width.max(1),
                height: height.max(1),
                depth_or_array_layers: 1,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::Depth32Float,
            usage: wgpu::TextureUsages::RENDER_ATTACHMENT | wgpu::TextureUsages::TEXTURE_BINDING,
            view_formats: &[],
        });
        let view = texture.create_view(&wgpu::TextureViewDescriptor::default());
        (texture, view)
    }

    pub fn resize(&mut self, new_size: PhysicalSize<u32>) {
        if new_size.width > 0 && new_size.height > 0 {
            self.size = new_size;
            self.config.width = new_size.width;
            self.config.height = new_size.height;
            self.surface.configure(&self.device, &self.config);

            // Recreate depth buffer
            let (depth_texture, depth_view) =
                Self::create_depth_texture(&self.device, new_size.width, new_size.height);
            self.depth_texture = depth_texture;
            self.depth_view = depth_view;

            // Update camera aspect ratio
            self.camera.set_aspect(new_size.width as f32 / new_size.height as f32);

            tracing::debug!("Resized to {}x{}", new_size.width, new_size.height);
        }
    }

    /// Register a mesh from MeshData. Returns the mesh name for later use.
    pub fn register_mesh(&mut self, name: &str, data: &MeshData) -> String {
        if self.mesh_cache.contains_key(name) {
            return name.to_string();
        }

        let vertex_buffer = self.device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some(&format!("mesh_{}_vertices", name)),
            contents: bytemuck::cast_slice(&data.vertices),
            usage: wgpu::BufferUsages::VERTEX,
        });

        self.mesh_cache.insert(
            name.to_string(),
            GpuMesh {
                vertex_buffer,
                vertex_count: data.vertex_count(),
            },
        );

        name.to_string()
    }

    /// Begin a new frame. Call this before any draw calls.
    pub fn begin_frame(&mut self, delta_time: f32) {
        self.time += delta_time;

        // Update global uniforms
        let global_uniforms = GlobalUniforms::new(
            self.camera.projection_matrix(),
            self.camera.view_matrix(),
            self.camera.position(),
            self.time,
        );
        self.phong_pipeline.update_global_uniforms(&self.queue, &global_uniforms);
    }

    /// Draw a 3D mesh with Phong shading.
    pub fn draw_mesh(
        &mut self,
        mesh_name: &str,
        position: Vec3,
        scale: Vec3,
        rotation: Vec3, // Euler angles in radians (X, Y, Z)
        color: Vec4,    // RGBA color
        encoder: &mut wgpu::CommandEncoder,
        view: &TextureView,
    ) {
        let mesh = match self.mesh_cache.get(mesh_name) {
            Some(m) => m,
            None => {
                tracing::warn!("Mesh not found: {}", mesh_name);
                return;
            }
        };

        // Build model matrix: scale -> rotate -> translate
        let model = Mat4::from_translation(position)
            * Mat4::from_euler(glam::EulerRot::ZYX, rotation.z, rotation.y, rotation.x)
            * Mat4::from_scale(scale);

        // Update instance uniforms
        let instance_uniforms = InstanceUniforms::new(model, color);
        self.queue.write_buffer(
            &self.instance_buffer,
            0,
            bytemuck::cast_slice(&[instance_uniforms]),
        );

        // Render
        {
            let mut render_pass = encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: Some("phong_render_pass"),
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view,
                    resolve_target: None,
                    ops: wgpu::Operations {
                        load: wgpu::LoadOp::Load, // Don't clear - we're accumulating draws
                        store: wgpu::StoreOp::Store,
                    },
                })],
                depth_stencil_attachment: Some(wgpu::RenderPassDepthStencilAttachment {
                    view: &self.depth_view,
                    depth_ops: Some(wgpu::Operations {
                        load: wgpu::LoadOp::Load,
                        store: wgpu::StoreOp::Store,
                    }),
                    stencil_ops: None,
                }),
                timestamp_writes: None,
                occlusion_query_set: None,
            });

            render_pass.set_pipeline(&self.phong_pipeline.pipeline);
            render_pass.set_bind_group(0, &self.phong_pipeline.global_bind_group, &[]);
            render_pass.set_bind_group(1, &self.instance_bind_group, &[]);
            render_pass.set_vertex_buffer(0, mesh.vertex_buffer.slice(..));
            render_pass.draw(0..mesh.vertex_count, 0..1);
        }
    }

    /// Render the frame. Returns the surface texture for presentation.
    pub fn render(&mut self) -> Result<(), wgpu::SurfaceError> {
        let output = self.surface.get_current_texture()?;
        let view = output
            .texture
            .create_view(&wgpu::TextureViewDescriptor::default());

        let mut encoder = self
            .device
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
                        load: wgpu::LoadOp::Clear(self.clear_color),
                        store: wgpu::StoreOp::Store,
                    },
                })],
                depth_stencil_attachment: Some(wgpu::RenderPassDepthStencilAttachment {
                    view: &self.depth_view,
                    depth_ops: Some(wgpu::Operations {
                        load: wgpu::LoadOp::Clear(1.0),
                        store: wgpu::StoreOp::Store,
                    }),
                    stencil_ops: None,
                }),
                timestamp_writes: None,
                occlusion_query_set: None,
            });
            // Pass drops here, ending the clear
        }

        // Draw a test mesh if registered
        if self.mesh_cache.contains_key("test_box") {
            self.draw_mesh(
                "test_box",
                Vec3::new(0.0, 0.0, 0.0),
                Vec3::splat(100.0),
                Vec3::new(0.0, self.time * 0.5, self.time * 0.3),
                Vec4::new(0.8, 0.3, 0.2, 1.0),
                &mut encoder,
                &view,
            );
        }

        self.queue.submit(std::iter::once(encoder.finish()));
        output.present();

        Ok(())
    }

    /// Get the camera for manipulation.
    pub fn camera(&self) -> &Camera {
        &self.camera
    }

    /// Get mutable camera reference.
    pub fn camera_mut(&mut self) -> &mut Camera {
        &mut self.camera
    }

    pub fn device(&self) -> &Device {
        &self.device
    }

    pub fn queue(&self) -> &Queue {
        &self.queue
    }

    pub fn surface(&self) -> &Surface<'static> {
        &self.surface
    }

    pub fn depth_view(&self) -> &TextureView {
        &self.depth_view
    }

    pub fn size(&self) -> PhysicalSize<u32> {
        self.size
    }

    pub fn time(&self) -> f32 {
        self.time
    }
}
