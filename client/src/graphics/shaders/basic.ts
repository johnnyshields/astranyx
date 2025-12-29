export const VERTEX_SHADER = `#version 300 es
precision highp float;

layout(location = 0) in vec3 aPosition;
layout(location = 1) in vec3 aNormal;

uniform mat4 uProjection;
uniform mat4 uView;
uniform mat4 uModel;
uniform float uTime;

out vec3 vNormal;
out vec3 vWorldPos;
out float vTime;

void main() {
  vec4 worldPos = uModel * vec4(aPosition, 1.0);
  vWorldPos = worldPos.xyz;
  vNormal = mat3(uModel) * aNormal;
  vTime = uTime;

  gl_Position = uProjection * uView * worldPos;
}
`

export const FRAGMENT_SHADER = `#version 300 es
precision highp float;

in vec3 vNormal;
in vec3 vWorldPos;
in float vTime;

uniform vec4 uColor;

out vec4 fragColor;

void main() {
  // Basic lighting
  vec3 lightDir = normalize(vec3(0.5, 0.7, 1.0));
  vec3 normal = normalize(vNormal);

  float diffuse = max(dot(normal, lightDir), 0.0);
  float ambient = 0.3;

  // Add subtle rim lighting for that sci-fi look
  vec3 viewDir = normalize(vec3(0.0, 0.0, 1.0));
  float rim = 1.0 - max(dot(viewDir, normal), 0.0);
  rim = pow(rim, 3.0) * 0.5;

  vec3 color = uColor.rgb * (ambient + diffuse * 0.7) + rim * uColor.rgb;

  // Slight pulsing glow for energy effects
  float pulse = sin(vTime * 3.0) * 0.1 + 0.9;
  color *= pulse;

  fragColor = vec4(color, uColor.a);
}
`

// Glow/bloom shader for post-processing (future use)
export const GLOW_FRAGMENT = `#version 300 es
precision highp float;

in vec2 vTexCoord;

uniform sampler2D uTexture;
uniform vec2 uResolution;
uniform float uIntensity;

out vec4 fragColor;

void main() {
  vec4 color = texture(uTexture, vTexCoord);

  // Simple box blur for bloom
  vec2 texelSize = 1.0 / uResolution;
  vec4 blur = vec4(0.0);

  for (int x = -2; x <= 2; x++) {
    for (int y = -2; y <= 2; y++) {
      blur += texture(uTexture, vTexCoord + vec2(float(x), float(y)) * texelSize);
    }
  }
  blur /= 25.0;

  fragColor = color + blur * uIntensity;
}
`
