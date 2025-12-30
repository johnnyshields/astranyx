# Three.js WebGPU Migration

**Date**: 2025-12-31
**Status**: Complete

## Overview

Migrating from raw WebGL2 to Three.js with WebGPU rendering (WebGL fallback).

## User Choices
- **WebGPU fallback**: WebGPU + WebGL fallback (try WebGPU first)
- **Materials**: Use built-in MeshPhongMaterial
- **Migration**: Big bang replacement

## Files to Modify

| File | Action | Changes |
|------|--------|---------|
| `client/package.json` | Modify | Add `three` dependency |
| `client/src/core/Renderer.ts` | **Replace** | Complete rewrite using Three.js |
| `client/src/core/Engine.ts` | Modify | Update renderer init (async) |
| `client/src/boot/Boot.ts` | Modify | Replace WebGL2 check with WebGPU/WebGL check |
| `client/src/graphics/shaders/*` | Keep | No longer used, keep for reference |
| `client/src/graphics/shaderUtils.ts` | Keep | No longer used |
| `client/src/game/Game.ts` | Modify | Update MeshHandle type import |

## Current Architecture

### Renderer.ts (847 lines)
- WebGL2 context with manual VAO/VBO management
- Single shader program (Blinn-Phong + rim lighting)
- Manual 4x4 matrix math (perspective, view, model, normal)
- 2.5D Einhänder-style camera (20° tilt, 900 unit distance)
- 5:3 aspect ratio with letterbox/pillarbox
- Methods: `init()`, `resize()`, `beginFrame()`, `endFrame()`, `createMesh()`, `loadGLB()`, `drawMesh()`, `drawQuad()`, `beginHUD()`, `endHUD()`, `worldToScreen()`, `getPlayBounds()`

### MeshHandle Interface (old)
```typescript
interface MeshHandle {
  vao: WebGLVertexArrayObject
  vbo: WebGLBuffer
  vertexCount: number
}
```

### MeshData Format
```typescript
interface MeshData {
  vertices: Float32Array  // Interleaved: x, y, z, nx, ny, nz (6 floats per vertex)
  vertexCount: number
}
```

## New Architecture

### ThreeRenderer Structure
```typescript
import * as THREE from 'three'
import WebGPURenderer from 'three/addons/renderers/webgpu/WebGPURenderer.js'
import { GLTFLoader } from 'three/addons/loaders/GLTFLoader.js'

interface MeshHandle {
  geometry: THREE.BufferGeometry
  baseMaterial: THREE.MeshPhongMaterial
}

class Renderer {
  private renderer: WebGPURenderer
  private scene: THREE.Scene
  private camera: THREE.PerspectiveCamera
  private orthoCamera: THREE.OrthographicCamera
  private gltfLoader: GLTFLoader
  private directionalLight: THREE.DirectionalLight
  private ambientLight: THREE.AmbientLight
  private meshCache: Map<string, MeshHandle>
  private frameObjects: THREE.Object3D[]  // Cleared each frame
}
```

### Key Method Mappings

| Old Method | Three.js Implementation |
|------------|------------------------|
| `init()` | Create WebGPURenderer with await init(), setup Scene, Camera, Lights |
| `resize()` | renderer.setSize(), camera.aspect, viewport/scissor |
| `beginFrame()` | Clear frameObjects from scene, update time |
| `endFrame()` | renderer.render(scene, camera) |
| `createMesh()` | Convert MeshData to BufferGeometry + MeshPhongMaterial |
| `loadGLB()` | Use GLTFLoader (replaces manual parsing) |
| `drawMesh()` | Create mesh with cloned material, add to scene |
| `drawQuad()` | Create PlaneGeometry mesh, add to scene |
| `beginHUD()` | Render 3D scene, switch to orthoCamera |
| `worldToScreen()` | THREE.Vector3.project() |
| `getPlayBounds()` | THREE.Raycaster to unproject corners |

### Camera Setup
```typescript
// Match existing Einhänder-style 2.5D camera
this.camera = new THREE.PerspectiveCamera(45, 5/3, 10, 2000)

const cameraDistance = 900
const cameraTiltAngle = 20 * (Math.PI / 180)

const camX = -cameraDistance * Math.sin(cameraTiltAngle)  // ~-308
const camY = 0
const camZ = cameraDistance * Math.cos(cameraTiltAngle)   // ~846

this.camera.position.set(camX, camY, camZ)
this.camera.lookAt(0, 0, 0)
```

### Lighting Setup
```typescript
// Match shader: vec3 lightDir = normalize(vec3(0.3, 0.5, 0.8))
this.directionalLight = new THREE.DirectionalLight(0xffffff, 0.6)
this.directionalLight.position.set(0.3, 0.5, 0.8).normalize()

// Match shader: float ambient = 0.25
this.ambientLight = new THREE.AmbientLight(0xffffff, 0.25)
```

### MeshData Conversion
```typescript
createMesh(name: string, data: MeshData): MeshHandle {
  const geometry = new THREE.BufferGeometry()

  // Split interleaved data
  const positions = new Float32Array(data.vertexCount * 3)
  const normals = new Float32Array(data.vertexCount * 3)

  for (let i = 0; i < data.vertexCount; i++) {
    positions[i*3+0] = data.vertices[i*6+0]
    positions[i*3+1] = data.vertices[i*6+1]
    positions[i*3+2] = data.vertices[i*6+2]
    normals[i*3+0] = data.vertices[i*6+3]
    normals[i*3+1] = data.vertices[i*6+4]
    normals[i*3+2] = data.vertices[i*6+5]
  }

  geometry.setAttribute('position', new THREE.BufferAttribute(positions, 3))
  geometry.setAttribute('normal', new THREE.BufferAttribute(normals, 3))

  const material = new THREE.MeshPhongMaterial({
    shininess: 32,
    specular: 0x404040,
    transparent: true,
  })

  return { geometry, baseMaterial: material }
}
```

## Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| Determinism for P2P | Three.js math is deterministic; verify with lockstep tests |
| Bundle size (+150KB) | Tree-shaking helps; acceptable for graphics upgrade |
| WebGPU browser support | Automatic WebGL fallback built-in |
| Visual differences | Match camera position, lighting exactly |

## Implementation Notes

### Key Fix: Manual GLB Parsing
The Three.js GLTFLoader didn't correctly load the custom GLB files. The solution was to keep the original manual GLB parsing code and create `THREE.BufferGeometry` directly:

```typescript
// Extract data from binary chunk
const positions = new Float32Array(binChunk, posView.byteOffset, posAccessor.count * 3)
const normals = new Float32Array(binChunk, normalView.byteOffset, normalAccessor.count * 3)

// Create Three.js BufferGeometry with separate position and normal attributes
const geometry = new THREE.BufferGeometry()
geometry.setAttribute('position', new THREE.BufferAttribute(positions.slice(), 3))
geometry.setAttribute('normal', new THREE.BufferAttribute(normals.slice(), 3))
```

### Materials
- `MeshPhongMaterial` for 3D meshes (shininess 32, specular 0x404040)
- `MeshBasicMaterial` for quads (DoubleSide)

### Lighting
- DirectionalLight at (300, 500, 800) with intensity 1.0
- AmbientLight with intensity 0.3

## Testing Checklist

- [x] `bun run typecheck` passes
- [x] Game renders (meshes visible)
- [ ] Camera angle matches
- [ ] Lighting/colors match
- [ ] All entity types render
- [ ] HUD overlay works
- [ ] Letterbox/pillarbox correct
- [ ] WebGL fallback works (Firefox)
- [ ] P2P multiplayer sync works
