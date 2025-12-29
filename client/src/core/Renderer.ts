import { createShader, createProgram } from '../graphics/shaderUtils.ts'
import { VERTEX_SHADER, FRAGMENT_SHADER } from '../graphics/shaders/basic.ts'

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

  // Geometry
  private quadVAO!: WebGLVertexArrayObject
  private quadVBO!: WebGLBuffer

  // Camera
  private viewMatrix = new Float32Array(16)
  private projectionMatrix = new Float32Array(16)

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

    // Update projection matrix (orthographic for 2.5D)
    // We use a coordinate system where (0,0) is center
    const aspectRatio = width / height
    const viewHeight = 600 // Virtual viewport height
    const viewWidth = viewHeight * aspectRatio

    this.setOrthographic(
      -viewWidth / 2, viewWidth / 2,
      -viewHeight / 2, viewHeight / 2,
      -1000, 1000
    )
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

    gl.uniformMatrix4fv(this.uModel, false, model)
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
