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
  private cameraPosition = new Float32Array([0, 200, 600])

  // Camera settings for 2.5D view
  private cameraTilt = 0.3  // Radians - tilt angle down

  // State
  private width = 0
  private height = 0
  private time = 0

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
    this.gl.viewport(0, 0, width, height)

    // Perspective projection for 2.5D look
    const aspectRatio = width / height
    const fov = 45 * (Math.PI / 180) // 45 degree field of view
    const near = 10
    const far = 2000

    this.setPerspective(fov, aspectRatio, near, far)

    // Set up camera view matrix with tilt
    this.setupCamera()
  }

  private setupCamera(): void {
    // Camera positioned above and back, looking down at a slight angle
    // This gives the Einhänder-style 2.5D view
    const camX = this.cameraPosition[0]!
    const camY = this.cameraPosition[1]!
    const camZ = this.cameraPosition[2]!

    // Look at center of play area
    const targetX = 0
    const targetY = 0
    const targetZ = 0

    this.setLookAt(
      camX, camY, camZ,
      targetX, targetY, targetZ,
      0, 0, 1  // Z is up in our world
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

    // Clear with dark blue-black background
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
}
