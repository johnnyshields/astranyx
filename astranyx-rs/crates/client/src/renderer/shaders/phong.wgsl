// Phong shader with rim lighting for 2.5D sci-fi aesthetic.
//
// Matches the original TypeScript/WebGL shader behavior.

// Uniforms shared by all instances
struct Uniforms {
    projection: mat4x4<f32>,
    view: mat4x4<f32>,
    camera_pos: vec3<f32>,
    time: f32,
}

// Per-instance uniforms
struct InstanceUniforms {
    model: mat4x4<f32>,
    normal_matrix: mat3x3<f32>,
    color: vec4<f32>,
}

@group(0) @binding(0)
var<uniform> uniforms: Uniforms;

@group(1) @binding(0)
var<uniform> instance: InstanceUniforms;

struct VertexInput {
    @location(0) position: vec3<f32>,
    @location(1) normal: vec3<f32>,
}

struct VertexOutput {
    @builtin(position) clip_position: vec4<f32>,
    @location(0) world_pos: vec3<f32>,
    @location(1) normal: vec3<f32>,
}

@vertex
fn vs_main(in: VertexInput) -> VertexOutput {
    var out: VertexOutput;

    let world_pos = instance.model * vec4<f32>(in.position, 1.0);
    out.world_pos = world_pos.xyz;

    // Use normal matrix for correct normal transformation with non-uniform scale
    out.normal = instance.normal_matrix * in.normal;

    out.clip_position = uniforms.projection * uniforms.view * world_pos;

    return out;
}

@fragment
fn fs_main(in: VertexOutput) -> @location(0) vec4<f32> {
    // Light direction (from above-right-forward)
    let light_dir = normalize(vec3<f32>(0.3, 0.5, 0.8));
    let normal = normalize(in.normal);

    // View direction from camera to fragment
    let view_dir = normalize(uniforms.camera_pos - in.world_pos);

    // Diffuse lighting
    let diffuse = max(dot(normal, light_dir), 0.0);

    // Specular lighting (Blinn-Phong)
    let half_dir = normalize(light_dir + view_dir);
    let spec_angle = max(dot(normal, half_dir), 0.0);
    let specular = pow(spec_angle, 32.0) * 0.5;

    // Ambient
    let ambient = 0.25;

    // Rim lighting (edge glow for sci-fi look)
    var rim = 1.0 - max(dot(view_dir, normal), 0.0);
    rim = pow(rim, 3.0) * 0.4;

    // Combine lighting
    var color = instance.color.rgb * (ambient + diffuse * 0.6);
    color = color + vec3<f32>(specular * 0.8);  // White specular highlight
    color = color + rim * instance.color.rgb * 0.6;  // Colored rim light

    // Subtle energy pulse for sci-fi effect
    let pulse = sin(uniforms.time * 2.0) * 0.05 + 0.95;
    color = color * pulse;

    return vec4<f32>(color, instance.color.a);
}
