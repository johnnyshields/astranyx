import * as THREE from 'three'
import { WebGPURenderer } from 'three/webgpu'
import type { MeshData } from '../graphics/MeshGenerator.ts'
import { SafeConsole } from './SafeConsole.ts'

export interface MeshHandle {
  geometry: THREE.BufferGeometry
  baseMaterial: THREE.MeshPhongMaterial
}

export class Renderer {
  private canvas: HTMLCanvasElement
  private renderer!: WebGPURenderer
  private scene!: THREE.Scene
  private camera!: THREE.PerspectiveCamera
  private orthoCamera!: THREE.OrthographicCamera

  // Lights
  private directionalLight!: THREE.DirectionalLight
  private ambientLight!: THREE.AmbientLight

  // Reusable geometries
  private quadGeometry!: THREE.PlaneGeometry

  // Mesh cache (same interface as before)
  private meshCache = new Map<string, MeshHandle>()

  // Per-frame objects (cleared each frame)
  private frameObjects: THREE.Object3D[] = []

  // Camera settings for Einhänder-style 2.5D view
  // Play area is X (horizontal, -500 to +500) x Y (vertical, -300 to +300)
  // Z is depth (into screen). Camera looks from +Z toward origin with slight tilt
  private cameraDistance = 900
  private cameraTiltAngle = 20 * (Math.PI / 180)  // 20 degrees tilt - right side away

  // State
  private width = 0
  private height = 0
  private time = 0

  // Viewport for 5:3 letterbox/pillarbox (screen-space, not tilted)
  private viewportX = 0
  private viewportY = 0
  private viewportWidth = 0
  private viewportHeight = 0

  // Background color
  private backgroundColor = new THREE.Color(0x020206)

  constructor(canvas: HTMLCanvasElement) {
    this.canvas = canvas
  }

  async init(): Promise<void> {
    // Create WebGPURenderer with WebGL fallback
    this.renderer = new WebGPURenderer({
      canvas: this.canvas,
      antialias: true,
    })

    // Initialize renderer (required for WebGPU)
    await this.renderer.init()

    // Check if WebGPU backend is active
    const backend = this.renderer.backend as { isWebGPUBackend?: boolean }
    const isWebGPU = backend.isWebGPUBackend === true
    SafeConsole.log(`Three.js Renderer initialized (${isWebGPU ? 'WebGPU' : 'WebGL'} backend)`)

    // Scene setup
    this.scene = new THREE.Scene()
    this.scene.background = this.backgroundColor

    // Perspective camera for main view (5:3 aspect)
    this.camera = new THREE.PerspectiveCamera(45, 5 / 3, 10, 2000)
    this.setupCamera()

    // Orthographic camera for HUD
    this.orthoCamera = new THREE.OrthographicCamera(-500, 500, 300, -300, -100, 100)

    // Lighting setup (match original shader behavior)
    this.setupLighting()

    // Reusable quad geometry
    this.quadGeometry = new THREE.PlaneGeometry(1, 1)
  }

  private setupCamera(): void {
    // Einhänder-style 2.5D camera:
    // Game coordinates: X = left/right, Y = up/down (screen), Z = depth
    // Camera is in front (positive Z), looking back at origin
    // TILTED so right side (positive X) is farther away
    const camX = -this.cameraDistance * Math.sin(this.cameraTiltAngle)  // Left of center
    const camY = 0
    const camZ = this.cameraDistance * Math.cos(this.cameraTiltAngle)   // In front

    this.camera.position.set(camX, camY, camZ)
    this.camera.lookAt(0, 0, 0)
    this.camera.updateProjectionMatrix()
  }

  private setupLighting(): void {
    // Match original shader: vec3 lightDir = normalize(vec3(0.3, 0.5, 0.8))
    // Position needs to be far from origin - Three.js normalizes direction internally
    this.directionalLight = new THREE.DirectionalLight(0xffffff, 1.0)
    this.directionalLight.position.set(300, 500, 800)
    this.scene.add(this.directionalLight)

    // Match original shader: float ambient = 0.25
    this.ambientLight = new THREE.AmbientLight(0xffffff, 0.3)
    this.scene.add(this.ambientLight)
  }

  resize(width: number, height: number): void {
    this.width = width
    this.height = height

    // Fixed 5:3 aspect ratio viewport (letterbox/pillarbox)
    const targetAspect = 5 / 3
    const screenAspect = width / height

    if (screenAspect > targetAspect) {
      // Screen is wider than target - pillarbox (black bars on sides)
      this.viewportHeight = height
      this.viewportWidth = Math.floor(height * targetAspect)
      this.viewportX = Math.floor((width - this.viewportWidth) / 2)
      this.viewportY = 0
    } else {
      // Screen is taller than target - letterbox (black bars on top/bottom)
      this.viewportWidth = width
      this.viewportHeight = Math.floor(width / targetAspect)
      this.viewportX = 0
      this.viewportY = Math.floor((height - this.viewportHeight) / 2)
    }

    // Update renderer size
    this.renderer.setSize(width, height)

    // Update camera aspect (always 5:3)
    this.camera.aspect = targetAspect
    this.camera.updateProjectionMatrix()

    // Update ortho camera for HUD
    const scale = 500 / (this.viewportWidth / 2)
    const halfW = this.viewportWidth / 2 * scale
    const halfH = this.viewportHeight / 2 * scale
    this.orthoCamera.left = -halfW
    this.orthoCamera.right = halfW
    this.orthoCamera.top = halfH
    this.orthoCamera.bottom = -halfH
    this.orthoCamera.updateProjectionMatrix()
  }

  beginFrame(deltaTime: number): void {
    this.time += deltaTime

    // Clear all objects added in the previous frame
    for (const obj of this.frameObjects) {
      this.scene.remove(obj)
      // Dispose geometry and material if they were created per-frame
      if (obj instanceof THREE.Mesh) {
        if (obj.geometry !== this.quadGeometry) {
          // Don't dispose cached geometries
        }
        if (obj.material instanceof THREE.Material) {
          obj.material.dispose()
        }
      }
    }
    this.frameObjects = []

    // Set viewport for letterbox/pillarbox
    // Three.js viewport Y is from bottom, so we need to flip
    const flippedY = this.height - this.viewportY - this.viewportHeight
    this.renderer.setViewport(this.viewportX, flippedY, this.viewportWidth, this.viewportHeight)
    this.renderer.setScissor(this.viewportX, flippedY, this.viewportWidth, this.viewportHeight)
    this.renderer.setScissorTest(true)
  }

  // Create a mesh from vertex data
  createMesh(name: string, data: MeshData): MeshHandle {
    // Check cache first
    const cached = this.meshCache.get(name)
    if (cached) return cached

    const geometry = new THREE.BufferGeometry()

    // Split interleaved data (position + normal per vertex)
    const positions = new Float32Array(data.vertexCount * 3)
    const normals = new Float32Array(data.vertexCount * 3)

    for (let i = 0; i < data.vertexCount; i++) {
      positions[i * 3 + 0] = data.vertices[i * 6 + 0]!
      positions[i * 3 + 1] = data.vertices[i * 6 + 1]!
      positions[i * 3 + 2] = data.vertices[i * 6 + 2]!
      normals[i * 3 + 0] = data.vertices[i * 6 + 3]!
      normals[i * 3 + 1] = data.vertices[i * 6 + 4]!
      normals[i * 3 + 2] = data.vertices[i * 6 + 5]!
    }

    geometry.setAttribute('position', new THREE.BufferAttribute(positions, 3))
    geometry.setAttribute('normal', new THREE.BufferAttribute(normals, 3))

    // Create material with Phong shading (matches original shader)
    const material = new THREE.MeshPhongMaterial({
      shininess: 32,  // Match shader: pow(specAngle, 32.0)
      specular: new THREE.Color(0x404040),
      transparent: true,
    })

    const handle: MeshHandle = { geometry, baseMaterial: material }
    this.meshCache.set(name, handle)
    return handle
  }

  // Load a mesh from a GLB file - parse manually to match original format
  async loadGLB(name: string, url: string): Promise<MeshHandle> {
    // Check cache first
    const cached = this.meshCache.get(name)
    if (cached) return cached

    const response = await fetch(url)
    const buffer = await response.arrayBuffer()

    // Parse GLB header
    const view = new DataView(buffer)
    const magic = view.getUint32(0, true)
    if (magic !== 0x46546C67) { // 'glTF'
      throw new Error(`Invalid GLB magic: ${magic.toString(16)}`)
    }

    // Parse chunks
    let offset = 12
    let jsonChunk: string | null = null
    let binChunk: ArrayBuffer | null = null

    while (offset < buffer.byteLength) {
      const chunkLength = view.getUint32(offset, true)
      const chunkType = view.getUint32(offset + 4, true)
      offset += 8

      if (chunkType === 0x4E4F534A) { // 'JSON'
        const decoder = new TextDecoder()
        jsonChunk = decoder.decode(new Uint8Array(buffer, offset, chunkLength))
      } else if (chunkType === 0x004E4942) { // 'BIN\0'
        binChunk = buffer.slice(offset, offset + chunkLength)
      }

      offset += chunkLength
    }

    if (!jsonChunk || !binChunk) {
      throw new Error('GLB missing JSON or BIN chunk')
    }

    // Parse glTF JSON
    const gltf = JSON.parse(jsonChunk) as {
      meshes: Array<{ primitives: Array<{ attributes: { POSITION: number; NORMAL: number } }> }>
      accessors: Array<{ bufferView: number; count: number }>
      bufferViews: Array<{ byteOffset: number; byteLength: number }>
    }

    // Get the first mesh's first primitive
    const mesh = gltf.meshes[0]!
    const primitive = mesh.primitives[0]!

    // Get position and normal accessors
    const posAccessor = gltf.accessors[primitive.attributes.POSITION]!
    const normalAccessor = gltf.accessors[primitive.attributes.NORMAL]!

    // Get buffer views
    const posView = gltf.bufferViews[posAccessor.bufferView]!
    const normalView = gltf.bufferViews[normalAccessor.bufferView]!

    // Extract data from binary chunk
    const positions = new Float32Array(binChunk, posView.byteOffset, posAccessor.count * 3)
    const normals = new Float32Array(binChunk, normalView.byteOffset, normalAccessor.count * 3)

    SafeConsole.log(`Loaded ${name}: ${posAccessor.count} vertices`)

    // Create Three.js BufferGeometry with separate position and normal attributes
    const geometry = new THREE.BufferGeometry()
    geometry.setAttribute('position', new THREE.BufferAttribute(positions.slice(), 3))
    geometry.setAttribute('normal', new THREE.BufferAttribute(normals.slice(), 3))

    // Create material
    const material = new THREE.MeshPhongMaterial({
      shininess: 32,
      specular: new THREE.Color(0x404040),
      transparent: true,
    })

    const handle: MeshHandle = { geometry, baseMaterial: material }
    this.meshCache.set(name, handle)
    return handle
  }

  // Draw a 3D mesh with full transformation
  drawMesh(
    mesh: MeshHandle,
    x: number, y: number, z: number,
    scaleX: number, scaleY: number, scaleZ: number,
    color: [number, number, number, number],
    rotationX = 0,
    rotationY = 0,
    rotationZ = 0
  ): void {
    // Create material with Phong shading
    const material = new THREE.MeshPhongMaterial({
      color: new THREE.Color(color[0], color[1], color[2]),
      shininess: 32,
      specular: new THREE.Color(0x404040),
      transparent: color[3] < 1,
      opacity: color[3],
      side: THREE.DoubleSide,
    })

    // Create mesh instance
    const meshObj = new THREE.Mesh(mesh.geometry, material)
    meshObj.position.set(x, y, z)
    meshObj.scale.set(scaleX, scaleY, scaleZ)

    // Apply rotations (Z * Y * X order to match original)
    meshObj.rotation.order = 'ZYX'
    meshObj.rotation.set(rotationX, rotationY, rotationZ)

    this.scene.add(meshObj)
    this.frameObjects.push(meshObj)
  }

  drawQuad(
    x: number, y: number, z: number,
    width: number, height: number,
    color: [number, number, number, number],
    rotation = 0
  ): void {
    const material = new THREE.MeshBasicMaterial({
      color: new THREE.Color(color[0], color[1], color[2]),
      transparent: true,
      opacity: color[3],
      side: THREE.DoubleSide,
      depthWrite: color[3] >= 1,
    })

    const mesh = new THREE.Mesh(this.quadGeometry, material)
    mesh.position.set(x, y, z)
    mesh.scale.set(width, height, 1)
    // Rotate to face camera (plane faces +Z by default, camera is at +Z looking at -Z)
    // No rotation needed since DoubleSide is set
    mesh.rotation.z = rotation

    this.scene.add(mesh)
    this.frameObjects.push(mesh)
  }

  endFrame(): void {
    this.renderer.render(this.scene, this.camera)
  }

  /**
   * Switch to HUD rendering mode - orthographic projection aligned with viewport.
   * HUD coordinates: X from -viewportWidth/2 to +viewportWidth/2, Y from -viewportHeight/2 to +viewportHeight/2
   * Normalized to roughly match game coordinate scale (scaled to fit 5:3 aspect)
   */
  beginHUD(): void {
    // Render the 3D scene first
    this.renderer.render(this.scene, this.camera)

    // Clear depth buffer so HUD renders on top
    this.renderer.clearDepth()
  }

  /**
   * End HUD mode and restore perspective projection
   */
  endHUD(): void {
    // Render HUD elements with orthographic camera
    this.renderer.render(this.scene, this.orthoCamera)
  }

  /**
   * Project a world coordinate (x, y, z=0) to HUD screen coordinates.
   * Returns coordinates in HUD space (roughly -500 to +500 range)
   */
  worldToScreen(worldX: number, worldY: number, worldZ: number = 0): { x: number, y: number } {
    const vector = new THREE.Vector3(worldX, worldY, worldZ)
    vector.project(this.camera)

    // Convert from NDC (-1 to 1) to HUD coordinates (roughly -500 to +500)
    const scale = 500 / (this.viewportWidth / 2)
    const halfW = this.viewportWidth / 2 * scale
    const halfH = this.viewportHeight / 2 * scale

    return {
      x: vector.x * halfW,
      y: vector.y * halfH
    }
  }

  getTime(): number {
    return this.time
  }

  getCameraTiltAngle(): number {
    return this.cameraTiltAngle
  }

  setCameraTiltAngle(angle: number): void {
    this.cameraTiltAngle = angle
    this.setupCamera()
  }

  /**
   * Calculate the world-space play bounds that map to the viewport edges.
   * This accounts for perspective and camera tilt so the game can constrain
   * entities to the visible area regardless of camera angle.
   *
   * Returns { leftX, rightX, topY, bottomY } at the z=0 plane
   * Also returns per-edge Y bounds since they vary with X due to perspective
   */
  getPlayBounds(): {
    leftX: number
    rightX: number
    getTopY: (x: number) => number
    getBottomY: (x: number) => number
  } {
    // Unproject viewport corners to z=0 plane using Three.js raycasting
    const plane = new THREE.Plane(new THREE.Vector3(0, 0, 1), 0)  // z=0 plane
    const raycaster = new THREE.Raycaster()

    const unproject = (ndcX: number, ndcY: number): THREE.Vector3 => {
      raycaster.setFromCamera(new THREE.Vector2(ndcX, ndcY), this.camera)
      const target = new THREE.Vector3()
      raycaster.ray.intersectPlane(plane, target)
      return target
    }

    // NDC corners: (-1,-1), (1,-1), (1,1), (-1,1) -> bottom-left, bottom-right, top-right, top-left
    const bottomLeft = unproject(-1, -1)
    const bottomRight = unproject(1, -1)
    const topRight = unproject(1, 1)
    const topLeft = unproject(-1, 1)

    // Due to perspective, left edge has different Y range than right edge
    const leftX = (bottomLeft.x + topLeft.x) / 2
    const rightX = (bottomRight.x + topRight.x) / 2 - 100  // Buffer on right side

    const leftBottomY = bottomLeft.y
    const leftTopY = topLeft.y
    const rightBottomY = bottomRight.y
    const rightTopY = topRight.y

    // Interpolate Y bounds based on X position
    const getTopY = (x: number): number => {
      const t = (x - leftX) / (rightX - leftX)
      return leftTopY + t * (rightTopY - leftTopY)
    }

    const getBottomY = (x: number): number => {
      const t = (x - leftX) / (rightX - leftX)
      return leftBottomY + t * (rightBottomY - leftBottomY)
    }

    return { leftX, rightX, getTopY, getBottomY }
  }

  // Expose Three.js objects for advanced usage
  getThreeRenderer(): WebGPURenderer {
    return this.renderer
  }

  getScene(): THREE.Scene {
    return this.scene
  }

  getCamera(): THREE.PerspectiveCamera {
    return this.camera
  }
}
