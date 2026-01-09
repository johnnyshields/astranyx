//! Phong shading render pipeline with uniform buffers.

use bytemuck::{Pod, Zeroable};
use glam::{Mat3, Mat4, Vec3, Vec4};
use wgpu::{util::DeviceExt, BindGroup, BindGroupLayout, Buffer, Device, Queue, RenderPipeline, TextureFormat};

use super::mesh::MeshVertex;

/// Shader source embedded at compile time.
const PHONG_SHADER: &str = include_str!("shaders/phong.wgsl");

/// Global uniforms (camera, time).
#[repr(C)]
#[derive(Copy, Clone, Debug, Pod, Zeroable)]
pub struct GlobalUniforms {
    pub projection: [[f32; 4]; 4],
    pub view: [[f32; 4]; 4],
    pub camera_pos: [f32; 3],
    pub time: f32,
}

impl GlobalUniforms {
    pub fn new(projection: Mat4, view: Mat4, camera_pos: Vec3, time: f32) -> Self {
        Self {
            projection: projection.to_cols_array_2d(),
            view: view.to_cols_array_2d(),
            camera_pos: camera_pos.into(),
            time,
        }
    }
}

/// Per-instance uniforms (model matrix, color).
#[repr(C)]
#[derive(Copy, Clone, Debug, Pod, Zeroable)]
pub struct InstanceUniforms {
    pub model: [[f32; 4]; 4],
    pub normal_matrix: [[f32; 4]; 3], // mat3x3 requires padding, so use 3 vec4s
    pub color: [f32; 4],
}

impl InstanceUniforms {
    pub fn new(model: Mat4, color: Vec4) -> Self {
        // Calculate normal matrix (inverse transpose of upper-left 3x3)
        let normal_mat = Mat3::from_mat4(model).inverse().transpose();

        Self {
            model: model.to_cols_array_2d(),
            // Pad mat3 columns to vec4 for alignment
            normal_matrix: [
                [normal_mat.x_axis.x, normal_mat.x_axis.y, normal_mat.x_axis.z, 0.0],
                [normal_mat.y_axis.x, normal_mat.y_axis.y, normal_mat.y_axis.z, 0.0],
                [normal_mat.z_axis.x, normal_mat.z_axis.y, normal_mat.z_axis.z, 0.0],
            ],
            color: color.into(),
        }
    }
}

/// Phong render pipeline resources.
pub struct PhongPipeline {
    pub pipeline: RenderPipeline,
    pub global_bind_group_layout: BindGroupLayout,
    pub instance_bind_group_layout: BindGroupLayout,
    pub global_uniform_buffer: Buffer,
    pub global_bind_group: BindGroup,
}

impl PhongPipeline {
    /// Create the Phong pipeline.
    pub fn new(device: &Device, format: TextureFormat) -> Self {
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("phong_shader"),
            source: wgpu::ShaderSource::Wgsl(PHONG_SHADER.into()),
        });

        // Global uniforms bind group layout (group 0)
        let global_bind_group_layout =
            device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("global_bind_group_layout"),
                entries: &[wgpu::BindGroupLayoutEntry {
                    binding: 0,
                    visibility: wgpu::ShaderStages::VERTEX | wgpu::ShaderStages::FRAGMENT,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Uniform,
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                }],
            });

        // Instance uniforms bind group layout (group 1)
        let instance_bind_group_layout =
            device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("instance_bind_group_layout"),
                entries: &[wgpu::BindGroupLayoutEntry {
                    binding: 0,
                    visibility: wgpu::ShaderStages::VERTEX | wgpu::ShaderStages::FRAGMENT,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Uniform,
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                }],
            });

        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("phong_pipeline_layout"),
            bind_group_layouts: &[&global_bind_group_layout, &instance_bind_group_layout],
            push_constant_ranges: &[],
        });

        let pipeline = device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("phong_pipeline"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &shader,
                entry_point: Some("vs_main"),
                buffers: &[MeshVertex::desc()],
                compilation_options: Default::default(),
            },
            fragment: Some(wgpu::FragmentState {
                module: &shader,
                entry_point: Some("fs_main"),
                targets: &[Some(wgpu::ColorTargetState {
                    format,
                    blend: Some(wgpu::BlendState::ALPHA_BLENDING),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
                compilation_options: Default::default(),
            }),
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::TriangleList,
                strip_index_format: None,
                front_face: wgpu::FrontFace::Ccw,
                cull_mode: None, // Disabled for debugging
                polygon_mode: wgpu::PolygonMode::Fill,
                unclipped_depth: false,
                conservative: false,
            },
            depth_stencil: Some(wgpu::DepthStencilState {
                format: wgpu::TextureFormat::Depth32Float,
                depth_write_enabled: true,
                depth_compare: wgpu::CompareFunction::Less,
                stencil: wgpu::StencilState::default(),
                bias: wgpu::DepthBiasState::default(),
            }),
            multisample: wgpu::MultisampleState {
                count: 1,
                mask: !0,
                alpha_to_coverage_enabled: false,
            },
            multiview: None,
            cache: None,
        });

        // Create global uniform buffer
        let global_uniforms = GlobalUniforms::new(
            Mat4::IDENTITY,
            Mat4::IDENTITY,
            Vec3::ZERO,
            0.0,
        );

        let global_uniform_buffer = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("global_uniform_buffer"),
            contents: bytemuck::cast_slice(&[global_uniforms]),
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        });

        let global_bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("global_bind_group"),
            layout: &global_bind_group_layout,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: global_uniform_buffer.as_entire_binding(),
            }],
        });

        Self {
            pipeline,
            global_bind_group_layout,
            instance_bind_group_layout,
            global_uniform_buffer,
            global_bind_group,
        }
    }

    /// Update global uniforms.
    pub fn update_global_uniforms(&self, queue: &Queue, uniforms: &GlobalUniforms) {
        queue.write_buffer(&self.global_uniform_buffer, 0, bytemuck::cast_slice(&[*uniforms]));
    }

    /// Create an instance bind group.
    pub fn create_instance_bind_group(&self, device: &Device, buffer: &Buffer) -> BindGroup {
        device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("instance_bind_group"),
            layout: &self.instance_bind_group_layout,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: buffer.as_entire_binding(),
            }],
        })
    }
}
