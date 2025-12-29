import { createShader, createProgram } from '../graphics/shaderUtils.ts'
import { VERTEX_SHADER, FRAGMENT_SHADER } from '../graphics/shaders/basic.ts'
import type { MeshData } from '../graphics/MeshGenerator.ts'

export interface RenderCommand {
  type: 'quad' | 'mesh'
  x: number
  y: number
  z: number
  width: number
  height: number
  color: [number, number, number, number]
  rotation?: number
}

export interface MeshHandle {
  vao: WebGLVertexArrayObject
  vbo: WebGLBuffer
  vertexCount: number
}

export class Renderer {
  private canvas: HTMLCanvasElement
  private gl!: WebGL2RenderingContext
  private program!: WebGLProgram

  // Uniforms
  private uProjection!: WebGLUniformLocation
  private uView!: WebGLUniformLocation
  private uModel!: WebGLUniformLocation
  private uColor!: WebGLUniformLocation
  private uTime!: WebGLUniformLocation
  private uCameraPos!: WebGLUniformLocation
  private uNormalMatrix!: WebGLUniformLocation

  // Geometry
  private quadVAO!: WebGLVertexArrayObject
  private quadVBO!: WebGLBuffer

  // Cached meshes
  private meshCache = new Map<string, MeshHandle>()

  // Camera
  private viewMatrix = new Float32Array(16)
  private projectionMatrix = new Float32Array(16)
  private normalMatrix = new Float32Array(9)
  private cameraPosition = new Float32Array(3)

  // Camera settings for Einhänder-style 2.5D view
  // Play area is X (horizontal, -500 to +500) x Y (vertical, -300 to +300)
  // Z is depth (into screen). Camera looks from +Z toward origin with slight downward tilt
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

  constructor(canvas: HTMLCanvasElement) {
    this.canvas = canvas
  }

  async init(): Promise<void> {
    const gl = this.canvas.getContext('webgl2', {
      alpha: false,
      antialias: true,
      depth: true,
      stencil: false,
      powerPreference: 'high-performance',
    })

    if (!gl) {
      throw new Error('WebGL2 not supported')
    }

    this.gl = gl

    // Enable depth testing for 2.5D layering
    gl.enable(gl.DEPTH_TEST)
    gl.depthFunc(gl.LEQUAL)

    // Enable blending for transparency
    gl.enable(gl.BLEND)
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA)

    // Compile shaders
    await this.initShaders()

    // Create geometry
    this.initGeometry()

    // Initialize matrices to identity
    this.setIdentity(this.viewMatrix)
    this.setIdentity(this.projectionMatrix)

    console.log('WebGL2 Renderer initialized')
    console.log('Max texture size:', gl.getParameter(gl.MAX_TEXTURE_SIZE))
  }

  private async initShaders(): Promise<void> {
    const gl = this.gl

    const vertexShader = createShader(gl, gl.VERTEX_SHADER, VERTEX_SHADER)
    const fragmentShader = createShader(gl, gl.FRAGMENT_SHADER, FRAGMENT_SHADER)

    this.program = createProgram(gl, vertexShader, fragmentShader)

    // Get uniform locations
    this.uProjection = gl.getUniformLocation(this.program, 'uProjection')!
    this.uView = gl.getUniformLocation(this.program, 'uView')!
    this.uModel = gl.getUniformLocation(this.program, 'uModel')!
    this.uColor = gl.getUniformLocation(this.program, 'uColor')!
    this.uTime = gl.getUniformLocation(this.program, 'uTime')!
    this.uCameraPos = gl.getUniformLocation(this.program, 'uCameraPos')!
    this.uNormalMatrix = gl.getUniformLocation(this.program, 'uNormalMatrix')!
  }

  private initGeometry(): void {
    const gl = this.gl

    // Simple quad vertices (position + normal)
    const vertices = new Float32Array([
      // Position (x, y, z), Normal (nx, ny, nz)
      -0.5, -0.5, 0,  0, 0, 1,
       0.5, -0.5, 0,  0, 0, 1,
       0.5,  0.5, 0,  0, 0, 1,
      -0.5, -0.5, 0,  0, 0, 1,
       0.5,  0.5, 0,  0, 0, 1,
      -0.5,  0.5, 0,  0, 0, 1,
    ])

    this.quadVAO = gl.createVertexArray()!
    this.quadVBO = gl.createBuffer()!

    gl.bindVertexArray(this.quadVAO)
    gl.bindBuffer(gl.ARRAY_BUFFER, this.quadVBO)
    gl.bufferData(gl.ARRAY_BUFFER, vertices, gl.STATIC_DRAW)

    // Position attribute
    gl.enableVertexAttribArray(0)
    gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 24, 0)

    // Normal attribute
    gl.enableVertexAttribArray(1)
    gl.vertexAttribPointer(1, 3, gl.FLOAT, false, 24, 12)

    gl.bindVertexArray(null)
  }

  resize(width: number, height: number): void {
    this.width = width
    this.height = height

    // Fixed 5:3 aspect ratio viewport (letterbox/pillarbox)
    // This is screen-space, not affected by game camera tilt
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

    // Perspective projection for 2.5D look (always 5:3)
    const fov = 45 * (Math.PI / 180) // 45 degree field of view
    const near = 10
    const far = 2000

    this.setPerspective(fov, targetAspect, near, far)

    // Set up camera view matrix with tilt
    this.setupCamera()
  }

  private setupCamera(): void {
    // Einhänder-style 2.5D camera:
    // Game coordinates: X = left/right, Y = up/down (screen), Z = depth
    // Camera is in front (positive Z), looking back at origin
    // TILTED so right side (positive X) is farther away - like viewing from left side of a table

    // Camera positioned in front and to the LEFT of play area
    // This makes right side of screen tilt away
    const camX = -this.cameraDistance * Math.sin(this.cameraTiltAngle)  // Left of center
    const camY = 0
    const camZ = this.cameraDistance * Math.cos(this.cameraTiltAngle)   // In front

    this.cameraPosition[0] = camX
    this.cameraPosition[1] = camY
    this.cameraPosition[2] = camZ

    // Look at center of play area
    const targetX = 0
    const targetY = 0
    const targetZ = 0

    this.setLookAt(
      camX, camY, camZ,
      targetX, targetY, targetZ,
      0, 1, 0  // Y is up in screen space
    )
  }

  private setPerspective(fov: number, aspect: number, near: number, far: number): void {
    const m = this.projectionMatrix
    const f = 1.0 / Math.tan(fov / 2)

    m[0] = f / aspect
    m[1] = 0
    m[2] = 0
    m[3] = 0
    m[4] = 0
    m[5] = f
    m[6] = 0
    m[7] = 0
    m[8] = 0
    m[9] = 0
    m[10] = (far + near) / (near - far)
    m[11] = -1
    m[12] = 0
    m[13] = 0
    m[14] = (2 * far * near) / (near - far)
    m[15] = 0
  }

  private setLookAt(
    eyeX: number, eyeY: number, eyeZ: number,
    targetX: number, targetY: number, targetZ: number,
    upX: number, upY: number, upZ: number
  ): void {
    const m = this.viewMatrix

    // Calculate forward vector (from eye to target)
    let fx = targetX - eyeX
    let fy = targetY - eyeY
    let fz = targetZ - eyeZ
    let len = Math.sqrt(fx * fx + fy * fy + fz * fz)
    if (len > 0) { fx /= len; fy /= len; fz /= len }

    // Calculate right vector (forward x up)
    let rx = fy * upZ - fz * upY
    let ry = fz * upX - fx * upZ
    let rz = fx * upY - fy * upX
    len = Math.sqrt(rx * rx + ry * ry + rz * rz)
    if (len > 0) { rx /= len; ry /= len; rz /= len }

    // Calculate true up vector (right x forward)
    const ux = ry * fz - rz * fy
    const uy = rz * fx - rx * fz
    const uz = rx * fy - ry * fx

    // Build view matrix
    m[0] = rx; m[1] = ux; m[2] = -fx; m[3] = 0
    m[4] = ry; m[5] = uy; m[6] = -fy; m[7] = 0
    m[8] = rz; m[9] = uz; m[10] = -fz; m[11] = 0
    m[12] = -(rx * eyeX + ry * eyeY + rz * eyeZ)
    m[13] = -(ux * eyeX + uy * eyeY + uz * eyeZ)
    m[14] = (fx * eyeX + fy * eyeY + fz * eyeZ)
    m[15] = 1
  }

  private setOrthographic(
    left: number, right: number,
    bottom: number, top: number,
    near: number, far: number
  ): void {
    const m = this.projectionMatrix
    m[0] = 2 / (right - left)
    m[1] = 0
    m[2] = 0
    m[3] = 0
    m[4] = 0
    m[5] = 2 / (top - bottom)
    m[6] = 0
    m[7] = 0
    m[8] = 0
    m[9] = 0
    m[10] = -2 / (far - near)
    m[11] = 0
    m[12] = -(right + left) / (right - left)
    m[13] = -(top + bottom) / (top - bottom)
    m[14] = -(far + near) / (far - near)
    m[15] = 1
  }

  private setIdentity(m: Float32Array): void {
    m.fill(0)
    m[0] = m[5] = m[10] = m[15] = 1
  }

  beginFrame(deltaTime: number): void {
    this.time += deltaTime
    const gl = this.gl

    // First: clear entire screen to black (letterbox/pillarbox bars)
    gl.disable(gl.SCISSOR_TEST)
    gl.viewport(0, 0, this.width, this.height)
    gl.clearColor(0, 0, 0, 1.0)
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT)

    // Then: set viewport to 5:3 game area and clear with game background
    gl.viewport(this.viewportX, this.viewportY, this.viewportWidth, this.viewportHeight)
    gl.enable(gl.SCISSOR_TEST)
    gl.scissor(this.viewportX, this.viewportY, this.viewportWidth, this.viewportHeight)
    gl.clearColor(0.02, 0.02, 0.06, 1.0)
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT)

    // Use shader program
    gl.useProgram(this.program)

    // Set common uniforms
    gl.uniformMatrix4fv(this.uProjection, false, this.projectionMatrix)
    gl.uniformMatrix4fv(this.uView, false, this.viewMatrix)
    gl.uniform1f(this.uTime, this.time)
    gl.uniform3fv(this.uCameraPos, this.cameraPosition)
  }

  // Create a mesh from vertex data
  createMesh(name: string, data: MeshData): MeshHandle {
    // Check cache first
    const cached = this.meshCache.get(name)
    if (cached) return cached

    const gl = this.gl

    const vao = gl.createVertexArray()!
    const vbo = gl.createBuffer()!

    gl.bindVertexArray(vao)
    gl.bindBuffer(gl.ARRAY_BUFFER, vbo)
    gl.bufferData(gl.ARRAY_BUFFER, data.vertices, gl.STATIC_DRAW)

    // Position attribute (location 0)
    gl.enableVertexAttribArray(0)
    gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 24, 0)

    // Normal attribute (location 1)
    gl.enableVertexAttribArray(1)
    gl.vertexAttribPointer(1, 3, gl.FLOAT, false, 24, 12)

    gl.bindVertexArray(null)

    const handle: MeshHandle = { vao, vbo, vertexCount: data.vertexCount }
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
    const gl = this.gl

    // Build model matrix with rotation
    const model = new Float32Array(16)
    this.setIdentity(model)

    // Apply rotations (Z * Y * X order)
    if (rotationZ !== 0) {
      this.rotateZ(model, rotationZ)
    }
    if (rotationY !== 0) {
      this.rotateY(model, rotationY)
    }
    if (rotationX !== 0) {
      this.rotateX(model, rotationX)
    }

    // Apply scale
    model[0]! *= scaleX
    model[1]! *= scaleX
    model[2]! *= scaleX
    model[4]! *= scaleY
    model[5]! *= scaleY
    model[6]! *= scaleY
    model[8]! *= scaleZ
    model[9]! *= scaleZ
    model[10]! *= scaleZ

    // Apply translation
    model[12] = x
    model[13] = y
    model[14] = z

    // Calculate normal matrix (inverse transpose of model matrix 3x3)
    this.computeNormalMatrix(model)

    gl.uniformMatrix4fv(this.uModel, false, model)
    gl.uniformMatrix3fv(this.uNormalMatrix, false, this.normalMatrix)
    gl.uniform4fv(this.uColor, color)

    gl.bindVertexArray(mesh.vao)
    gl.drawArrays(gl.TRIANGLES, 0, mesh.vertexCount)
  }

  private rotateX(m: Float32Array, angle: number): void {
    const c = Math.cos(angle)
    const s = Math.sin(angle)
    const m4 = m[4]!, m5 = m[5]!, m6 = m[6]!, m7 = m[7]!
    const m8 = m[8]!, m9 = m[9]!, m10 = m[10]!, m11 = m[11]!
    m[4] = m4 * c + m8 * s
    m[5] = m5 * c + m9 * s
    m[6] = m6 * c + m10 * s
    m[7] = m7 * c + m11 * s
    m[8] = m8 * c - m4 * s
    m[9] = m9 * c - m5 * s
    m[10] = m10 * c - m6 * s
    m[11] = m11 * c - m7 * s
  }

  private rotateY(m: Float32Array, angle: number): void {
    const c = Math.cos(angle)
    const s = Math.sin(angle)
    const m0 = m[0]!, m1 = m[1]!, m2 = m[2]!, m3 = m[3]!
    const m8 = m[8]!, m9 = m[9]!, m10 = m[10]!, m11 = m[11]!
    m[0] = m0 * c - m8 * s
    m[1] = m1 * c - m9 * s
    m[2] = m2 * c - m10 * s
    m[3] = m3 * c - m11 * s
    m[8] = m0 * s + m8 * c
    m[9] = m1 * s + m9 * c
    m[10] = m2 * s + m10 * c
    m[11] = m3 * s + m11 * c
  }

  private rotateZ(m: Float32Array, angle: number): void {
    const c = Math.cos(angle)
    const s = Math.sin(angle)
    const m0 = m[0]!, m1 = m[1]!, m2 = m[2]!, m3 = m[3]!
    const m4 = m[4]!, m5 = m[5]!, m6 = m[6]!, m7 = m[7]!
    m[0] = m0 * c + m4 * s
    m[1] = m1 * c + m5 * s
    m[2] = m2 * c + m6 * s
    m[3] = m3 * c + m7 * s
    m[4] = m4 * c - m0 * s
    m[5] = m5 * c - m1 * s
    m[6] = m6 * c - m2 * s
    m[7] = m7 * c - m3 * s
  }

  private computeNormalMatrix(model: Float32Array): void {
    // Extract 3x3 rotation/scale part and compute inverse transpose
    // For uniform scale, this is just the upper-left 3x3
    const nm = this.normalMatrix
    nm[0] = model[0]!
    nm[1] = model[1]!
    nm[2] = model[2]!
    nm[3] = model[4]!
    nm[4] = model[5]!
    nm[5] = model[6]!
    nm[6] = model[8]!
    nm[7] = model[9]!
    nm[8] = model[10]!
  }

  drawQuad(
    x: number, y: number, z: number,
    width: number, height: number,
    color: [number, number, number, number],
    rotation = 0
  ): void {
    const gl = this.gl

    // Build model matrix
    const model = new Float32Array(16)
    this.setIdentity(model)

    // Translation
    model[12] = x
    model[13] = y
    model[14] = z

    // Scale
    model[0] = width
    model[5] = height

    // Rotation around Z axis (for 2D rotation in 2.5D space)
    if (rotation !== 0) {
      const cos = Math.cos(rotation)
      const sin = Math.sin(rotation)
      const m0 = model[0]!
      const m1 = model[1]!
      const m4 = model[4]!
      const m5 = model[5]!
      model[0] = m0 * cos - m4 * sin
      model[1] = m1 * cos - m5 * sin
      model[4] = m0 * sin + m4 * cos
      model[5] = m1 * sin + m5 * cos
    }

    // Compute normal matrix for quad
    this.computeNormalMatrix(model)

    gl.uniformMatrix4fv(this.uModel, false, model)
    gl.uniformMatrix3fv(this.uNormalMatrix, false, this.normalMatrix)
    gl.uniform4fv(this.uColor, color)

    gl.bindVertexArray(this.quadVAO)
    gl.drawArrays(gl.TRIANGLES, 0, 6)
  }

  endFrame(): void {
    this.gl.bindVertexArray(null)
  }

  getGL(): WebGL2RenderingContext {
    return this.gl
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
    // Unproject viewport corners to z=0 plane
    // NDC corners: (-1,-1), (1,-1), (1,1), (-1,1) -> bottom-left, bottom-right, top-right, top-left

    // Build inverse view-projection matrix
    const vp = this.multiplyMatrices(this.projectionMatrix, this.viewMatrix)
    const invVP = this.invertMatrix(vp)

    // Unproject all four corners to z=0 plane
    const corners = [
      this.unprojectToZ0(invVP, -1, -1),  // bottom-left
      this.unprojectToZ0(invVP, 1, -1),   // bottom-right
      this.unprojectToZ0(invVP, 1, 1),    // top-right
      this.unprojectToZ0(invVP, -1, 1),   // top-left
    ]

    // Due to perspective, left edge has different Y range than right edge
    // Left edge: corners[0] (bottom-left) to corners[3] (top-left)
    // Right edge: corners[1] (bottom-right) to corners[2] (top-right)

    const leftX = (corners[0]!.x + corners[3]!.x) / 2
    const rightX = (corners[1]!.x + corners[2]!.x) / 2 - 100  // Buffer on right side

    const leftBottomY = corners[0]!.y
    const leftTopY = corners[3]!.y
    const rightBottomY = corners[1]!.y
    const rightTopY = corners[2]!.y

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

  /**
   * Unproject a normalized device coordinate point to the z=0 plane in world space.
   */
  private unprojectToZ0(invVP: Float32Array, ndcX: number, ndcY: number): { x: number, y: number } {
    // Create two points along the ray: near plane (z=-1) and far plane (z=1)
    const nearPoint = this.transformPoint(invVP, ndcX, ndcY, -1)
    const farPoint = this.transformPoint(invVP, ndcX, ndcY, 1)

    // Find where ray intersects z=0 plane
    // Ray: P = nearPoint + t * (farPoint - nearPoint)
    // At z=0: nearPoint.z + t * (farPoint.z - nearPoint.z) = 0
    const dz = farPoint.z - nearPoint.z
    if (Math.abs(dz) < 0.0001) {
      // Ray is parallel to z=0 plane, use near point
      return { x: nearPoint.x, y: nearPoint.y }
    }

    const t = -nearPoint.z / dz
    return {
      x: nearPoint.x + t * (farPoint.x - nearPoint.x),
      y: nearPoint.y + t * (farPoint.y - nearPoint.y),
    }
  }

  private transformPoint(m: Float32Array, x: number, y: number, z: number): { x: number, y: number, z: number } {
    const w = m[3]! * x + m[7]! * y + m[11]! * z + m[15]!
    return {
      x: (m[0]! * x + m[4]! * y + m[8]! * z + m[12]!) / w,
      y: (m[1]! * x + m[5]! * y + m[9]! * z + m[13]!) / w,
      z: (m[2]! * x + m[6]! * y + m[10]! * z + m[14]!) / w,
    }
  }

  private multiplyMatrices(a: Float32Array, b: Float32Array): Float32Array {
    const result = new Float32Array(16)
    for (let i = 0; i < 4; i++) {
      for (let j = 0; j < 4; j++) {
        result[i * 4 + j] =
          a[j]! * b[i * 4]! +
          a[j + 4]! * b[i * 4 + 1]! +
          a[j + 8]! * b[i * 4 + 2]! +
          a[j + 12]! * b[i * 4 + 3]!
      }
    }
    return result
  }

  private invertMatrix(m: Float32Array): Float32Array {
    const inv = new Float32Array(16)

    inv[0] = m[5]! * m[10]! * m[15]! - m[5]! * m[11]! * m[14]! - m[9]! * m[6]! * m[15]! +
             m[9]! * m[7]! * m[14]! + m[13]! * m[6]! * m[11]! - m[13]! * m[7]! * m[10]!
    inv[4] = -m[4]! * m[10]! * m[15]! + m[4]! * m[11]! * m[14]! + m[8]! * m[6]! * m[15]! -
             m[8]! * m[7]! * m[14]! - m[12]! * m[6]! * m[11]! + m[12]! * m[7]! * m[10]!
    inv[8] = m[4]! * m[9]! * m[15]! - m[4]! * m[11]! * m[13]! - m[8]! * m[5]! * m[15]! +
             m[8]! * m[7]! * m[13]! + m[12]! * m[5]! * m[11]! - m[12]! * m[7]! * m[9]!
    inv[12] = -m[4]! * m[9]! * m[14]! + m[4]! * m[10]! * m[13]! + m[8]! * m[5]! * m[14]! -
              m[8]! * m[6]! * m[13]! - m[12]! * m[5]! * m[10]! + m[12]! * m[6]! * m[9]!
    inv[1] = -m[1]! * m[10]! * m[15]! + m[1]! * m[11]! * m[14]! + m[9]! * m[2]! * m[15]! -
             m[9]! * m[3]! * m[14]! - m[13]! * m[2]! * m[11]! + m[13]! * m[3]! * m[10]!
    inv[5] = m[0]! * m[10]! * m[15]! - m[0]! * m[11]! * m[14]! - m[8]! * m[2]! * m[15]! +
             m[8]! * m[3]! * m[14]! + m[12]! * m[2]! * m[11]! - m[12]! * m[3]! * m[10]!
    inv[9] = -m[0]! * m[9]! * m[15]! + m[0]! * m[11]! * m[13]! + m[8]! * m[1]! * m[15]! -
             m[8]! * m[3]! * m[13]! - m[12]! * m[1]! * m[11]! + m[12]! * m[3]! * m[9]!
    inv[13] = m[0]! * m[9]! * m[14]! - m[0]! * m[10]! * m[13]! - m[8]! * m[1]! * m[14]! +
              m[8]! * m[2]! * m[13]! + m[12]! * m[1]! * m[10]! - m[12]! * m[2]! * m[9]!
    inv[2] = m[1]! * m[6]! * m[15]! - m[1]! * m[7]! * m[14]! - m[5]! * m[2]! * m[15]! +
             m[5]! * m[3]! * m[14]! + m[13]! * m[2]! * m[7]! - m[13]! * m[3]! * m[6]!
    inv[6] = -m[0]! * m[6]! * m[15]! + m[0]! * m[7]! * m[14]! + m[4]! * m[2]! * m[15]! -
             m[4]! * m[3]! * m[14]! - m[12]! * m[2]! * m[7]! + m[12]! * m[3]! * m[6]!
    inv[10] = m[0]! * m[5]! * m[15]! - m[0]! * m[7]! * m[13]! - m[4]! * m[1]! * m[15]! +
              m[4]! * m[3]! * m[13]! + m[12]! * m[1]! * m[7]! - m[12]! * m[3]! * m[5]!
    inv[14] = -m[0]! * m[5]! * m[14]! + m[0]! * m[6]! * m[13]! + m[4]! * m[1]! * m[14]! -
              m[4]! * m[2]! * m[13]! - m[12]! * m[1]! * m[6]! + m[12]! * m[2]! * m[5]!
    inv[3] = -m[1]! * m[6]! * m[11]! + m[1]! * m[7]! * m[10]! + m[5]! * m[2]! * m[11]! -
             m[5]! * m[3]! * m[10]! - m[9]! * m[2]! * m[7]! + m[9]! * m[3]! * m[6]!
    inv[7] = m[0]! * m[6]! * m[11]! - m[0]! * m[7]! * m[10]! - m[4]! * m[2]! * m[11]! +
             m[4]! * m[3]! * m[10]! + m[8]! * m[2]! * m[7]! - m[8]! * m[3]! * m[6]!
    inv[11] = -m[0]! * m[5]! * m[11]! + m[0]! * m[7]! * m[9]! + m[4]! * m[1]! * m[11]! -
              m[4]! * m[3]! * m[9]! - m[8]! * m[1]! * m[7]! + m[8]! * m[3]! * m[5]!
    inv[15] = m[0]! * m[5]! * m[10]! - m[0]! * m[6]! * m[9]! - m[4]! * m[1]! * m[10]! +
              m[4]! * m[2]! * m[9]! + m[8]! * m[1]! * m[6]! - m[8]! * m[2]! * m[5]!

    const det = m[0]! * inv[0]! + m[1]! * inv[4]! + m[2]! * inv[8]! + m[3]! * inv[12]!

    if (Math.abs(det) < 0.0001) {
      // Matrix is not invertible, return identity
      this.setIdentity(inv)
      return inv
    }

    const invDet = 1.0 / det
    for (let i = 0; i < 16; i++) {
      inv[i]! *= invDet
    }

    return inv
  }
}
