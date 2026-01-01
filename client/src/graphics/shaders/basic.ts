export const VERTEX_SHADER = `#version 300 es
precision highp float;

layout(location = 0) in vec3 aPosition;
layout(location = 1) in vec3 aNormal;

uniform mat4 uProjection;
uniform mat4 uView;
uniform mat4 uModel;
uniform mat3 uNormalMatrix;
uniform float uTime;

out vec3 vNormal;
out vec3 vWorldPos;
out float vTime;

void main() {
  vec4 worldPos = uModel * vec4(aPosition, 1.0);
  vWorldPos = worldPos.xyz;
  // Use normal matrix for correct normal transformation with non-uniform scale
  vNormal = uNormalMatrix * aNormal;
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
uniform vec3 uCameraPos;

out vec4 fragColor;

void main() {
  // Light direction (from above-right-forward)
  vec3 lightDir = normalize(vec3(0.3, 0.5, 0.8));
  vec3 normal = normalize(vNormal);

  // View direction from camera to fragment
  vec3 viewDir = normalize(uCameraPos - vWorldPos);

  // Diffuse lighting
  float diffuse = max(dot(normal, lightDir), 0.0);

  // Specular lighting (Blinn-Phong)
  vec3 halfDir = normalize(lightDir + viewDir);
  float specAngle = max(dot(normal, halfDir), 0.0);
  float specular = pow(specAngle, 32.0) * 0.5;

  // Ambient
  float ambient = 0.25;

  // Rim lighting (edge glow for sci-fi look)
  float rim = 1.0 - max(dot(viewDir, normal), 0.0);
  rim = pow(rim, 3.0) * 0.4;

  // Combine lighting
  vec3 color = uColor.rgb * (ambient + diffuse * 0.6);
  color += vec3(specular) * 0.8;  // White specular highlight
  color += rim * uColor.rgb * 0.6;  // Colored rim light

  // Subtle energy pulse for sci-fi effect
  float pulse = sin(vTime * 2.0) * 0.05 + 0.95;
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
