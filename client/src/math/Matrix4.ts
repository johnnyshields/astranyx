/**
 * 4x4 Matrix class for 3D transformations.
 * Uses column-major order (same as WebGL/OpenGL).
 * Elements stored as: [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]
 * Where columns are: [m0-m3], [m4-m7], [m8-m11], [m12-m15]
 */
export class Matrix4 {
  private data: Float32Array

  constructor(data?: Float32Array) {
    if (data) {
      this.data = new Float32Array(data)
    } else {
      this.data = new Float32Array(16)
      this.setIdentity()
    }
  }

  /**
   * Create an identity matrix
   */
  static identity(): Matrix4 {
    return new Matrix4()
  }

  /**
   * Create a zero matrix
   */
  static zero(): Matrix4 {
    const m = new Matrix4()
    m.data.fill(0)
    return m
  }

  /**
   * Get the underlying Float32Array (for WebGL uniforms)
   */
  getData(): Float32Array {
    return this.data
  }

  /**
   * Get element at row, column (0-indexed)
   */
  get(row: number, col: number): number {
    return this.data[col * 4 + row]!
  }

  /**
   * Set element at row, column (0-indexed)
   */
  set(row: number, col: number, value: number): this {
    this.data[col * 4 + row] = value
    return this
  }

  /**
   * Set this matrix to identity
   */
  setIdentity(): this {
    this.data.fill(0)
    this.data[0] = 1
    this.data[5] = 1
    this.data[10] = 1
    this.data[15] = 1
    return this
  }

  /**
   * Copy values from another matrix
   */
  copy(other: Matrix4): this {
    this.data.set(other.data)
    return this
  }

  /**
   * Create a copy of this matrix
   */
  clone(): Matrix4 {
    return new Matrix4(this.data)
  }

  /**
   * Multiply this matrix by another (this = this * other)
   */
  multiply(other: Matrix4): this {
    const a = this.data
    const b = other.data
    const result = new Float32Array(16)

    for (let col = 0; col < 4; col++) {
      for (let row = 0; row < 4; row++) {
        result[col * 4 + row] =
          a[row]! * b[col * 4]! +
          a[row + 4]! * b[col * 4 + 1]! +
          a[row + 8]! * b[col * 4 + 2]! +
          a[row + 12]! * b[col * 4 + 3]!
      }
    }

    this.data.set(result)
    return this
  }

  /**
   * Multiply this matrix by another (returns new matrix, this unchanged)
   */
  multiplied(other: Matrix4): Matrix4 {
    return this.clone().multiply(other)
  }

  /**
   * Pre-multiply this matrix by another (this = other * this)
   */
  preMultiply(other: Matrix4): this {
    const a = other.data
    const b = this.data
    const result = new Float32Array(16)

    for (let col = 0; col < 4; col++) {
      for (let row = 0; row < 4; row++) {
        result[col * 4 + row] =
          a[row]! * b[col * 4]! +
          a[row + 4]! * b[col * 4 + 1]! +
          a[row + 8]! * b[col * 4 + 2]! +
          a[row + 12]! * b[col * 4 + 3]!
      }
    }

    this.data.set(result)
    return this
  }

  /**
   * Set translation components
   */
  setTranslation(x: number, y: number, z: number): this {
    this.data[12] = x
    this.data[13] = y
    this.data[14] = z
    return this
  }

  /**
   * Get translation components
   */
  getTranslation(): { x: number; y: number; z: number } {
    return {
      x: this.data[12]!,
      y: this.data[13]!,
      z: this.data[14]!,
    }
  }

  /**
   * Apply translation (this = this * translate(x, y, z))
   */
  translate(x: number, y: number, z: number): this {
    const m = this.data
    m[12] = m[0]! * x + m[4]! * y + m[8]! * z + m[12]!
    m[13] = m[1]! * x + m[5]! * y + m[9]! * z + m[13]!
    m[14] = m[2]! * x + m[6]! * y + m[10]! * z + m[14]!
    m[15] = m[3]! * x + m[7]! * y + m[11]! * z + m[15]!
    return this
  }

  /**
   * Apply uniform scale
   */
  scale(s: number): this {
    return this.scaleXYZ(s, s, s)
  }

  /**
   * Apply non-uniform scale
   */
  scaleXYZ(sx: number, sy: number, sz: number): this {
    const m = this.data
    m[0]! *= sx; m[1]! *= sx; m[2]! *= sx; m[3]! *= sx
    m[4]! *= sy; m[5]! *= sy; m[6]! *= sy; m[7]! *= sy
    m[8]! *= sz; m[9]! *= sz; m[10]! *= sz; m[11]! *= sz
    return this
  }

  /**
   * Apply rotation around X axis
   */
  rotateX(angle: number): this {
    const c = Math.cos(angle)
    const s = Math.sin(angle)
    const m = this.data
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
    return this
  }

  /**
   * Apply rotation around Y axis
   */
  rotateY(angle: number): this {
    const c = Math.cos(angle)
    const s = Math.sin(angle)
    const m = this.data
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
    return this
  }

  /**
   * Apply rotation around Z axis
   */
  rotateZ(angle: number): this {
    const c = Math.cos(angle)
    const s = Math.sin(angle)
    const m = this.data
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
    return this
  }

  /**
   * Set this to a perspective projection matrix
   */
  setPerspective(fov: number, aspect: number, near: number, far: number): this {
    const f = 1.0 / Math.tan(fov / 2)
    const m = this.data

    m.fill(0)
    m[0] = f / aspect
    m[5] = f
    m[10] = (far + near) / (near - far)
    m[11] = -1
    m[14] = (2 * far * near) / (near - far)
    return this
  }

  /**
   * Set this to an orthographic projection matrix
   */
  setOrthographic(
    left: number,
    right: number,
    bottom: number,
    top: number,
    near: number,
    far: number
  ): this {
    const m = this.data
    m.fill(0)

    m[0] = 2 / (right - left)
    m[5] = 2 / (top - bottom)
    m[10] = -2 / (far - near)
    m[12] = -(right + left) / (right - left)
    m[13] = -(top + bottom) / (top - bottom)
    m[14] = -(far + near) / (far - near)
    m[15] = 1
    return this
  }

  /**
   * Set this to a look-at view matrix
   */
  setLookAt(
    eyeX: number,
    eyeY: number,
    eyeZ: number,
    targetX: number,
    targetY: number,
    targetZ: number,
    upX: number,
    upY: number,
    upZ: number
  ): this {
    const m = this.data

    // Calculate forward vector (from eye to target)
    let fx = targetX - eyeX
    let fy = targetY - eyeY
    let fz = targetZ - eyeZ
    let len = Math.sqrt(fx * fx + fy * fy + fz * fz)
    if (len > 0) {
      fx /= len
      fy /= len
      fz /= len
    }

    // Calculate right vector (forward x up)
    let rx = fy * upZ - fz * upY
    let ry = fz * upX - fx * upZ
    let rz = fx * upY - fy * upX
    len = Math.sqrt(rx * rx + ry * ry + rz * rz)
    if (len > 0) {
      rx /= len
      ry /= len
      rz /= len
    }

    // Calculate true up vector (right x forward)
    const ux = ry * fz - rz * fy
    const uy = rz * fx - rx * fz
    const uz = rx * fy - ry * fx

    // Build view matrix
    m[0] = rx
    m[1] = ux
    m[2] = -fx
    m[3] = 0
    m[4] = ry
    m[5] = uy
    m[6] = -fy
    m[7] = 0
    m[8] = rz
    m[9] = uz
    m[10] = -fz
    m[11] = 0
    m[12] = -(rx * eyeX + ry * eyeY + rz * eyeZ)
    m[13] = -(ux * eyeX + uy * eyeY + uz * eyeZ)
    m[14] = fx * eyeX + fy * eyeY + fz * eyeZ
    m[15] = 1
    return this
  }

  /**
   * Invert this matrix in place
   */
  invert(): this {
    const m = this.data
    const inv = new Float32Array(16)

    inv[0] =
      m[5]! * m[10]! * m[15]! -
      m[5]! * m[11]! * m[14]! -
      m[9]! * m[6]! * m[15]! +
      m[9]! * m[7]! * m[14]! +
      m[13]! * m[6]! * m[11]! -
      m[13]! * m[7]! * m[10]!
    inv[4] =
      -m[4]! * m[10]! * m[15]! +
      m[4]! * m[11]! * m[14]! +
      m[8]! * m[6]! * m[15]! -
      m[8]! * m[7]! * m[14]! -
      m[12]! * m[6]! * m[11]! +
      m[12]! * m[7]! * m[10]!
    inv[8] =
      m[4]! * m[9]! * m[15]! -
      m[4]! * m[11]! * m[13]! -
      m[8]! * m[5]! * m[15]! +
      m[8]! * m[7]! * m[13]! +
      m[12]! * m[5]! * m[11]! -
      m[12]! * m[7]! * m[9]!
    inv[12] =
      -m[4]! * m[9]! * m[14]! +
      m[4]! * m[10]! * m[13]! +
      m[8]! * m[5]! * m[14]! -
      m[8]! * m[6]! * m[13]! -
      m[12]! * m[5]! * m[10]! +
      m[12]! * m[6]! * m[9]!
    inv[1] =
      -m[1]! * m[10]! * m[15]! +
      m[1]! * m[11]! * m[14]! +
      m[9]! * m[2]! * m[15]! -
      m[9]! * m[3]! * m[14]! -
      m[13]! * m[2]! * m[11]! +
      m[13]! * m[3]! * m[10]!
    inv[5] =
      m[0]! * m[10]! * m[15]! -
      m[0]! * m[11]! * m[14]! -
      m[8]! * m[2]! * m[15]! +
      m[8]! * m[3]! * m[14]! +
      m[12]! * m[2]! * m[11]! -
      m[12]! * m[3]! * m[10]!
    inv[9] =
      -m[0]! * m[9]! * m[15]! +
      m[0]! * m[11]! * m[13]! +
      m[8]! * m[1]! * m[15]! -
      m[8]! * m[3]! * m[13]! -
      m[12]! * m[1]! * m[11]! +
      m[12]! * m[3]! * m[9]!
    inv[13] =
      m[0]! * m[9]! * m[14]! -
      m[0]! * m[10]! * m[13]! -
      m[8]! * m[1]! * m[14]! +
      m[8]! * m[2]! * m[13]! +
      m[12]! * m[1]! * m[10]! -
      m[12]! * m[2]! * m[9]!
    inv[2] =
      m[1]! * m[6]! * m[15]! -
      m[1]! * m[7]! * m[14]! -
      m[5]! * m[2]! * m[15]! +
      m[5]! * m[3]! * m[14]! +
      m[13]! * m[2]! * m[7]! -
      m[13]! * m[3]! * m[6]!
    inv[6] =
      -m[0]! * m[6]! * m[15]! +
      m[0]! * m[7]! * m[14]! +
      m[4]! * m[2]! * m[15]! -
      m[4]! * m[3]! * m[14]! -
      m[12]! * m[2]! * m[7]! +
      m[12]! * m[3]! * m[6]!
    inv[10] =
      m[0]! * m[5]! * m[15]! -
      m[0]! * m[7]! * m[13]! -
      m[4]! * m[1]! * m[15]! +
      m[4]! * m[3]! * m[13]! +
      m[12]! * m[1]! * m[7]! -
      m[12]! * m[3]! * m[5]!
    inv[14] =
      -m[0]! * m[5]! * m[14]! +
      m[0]! * m[6]! * m[13]! +
      m[4]! * m[1]! * m[14]! -
      m[4]! * m[2]! * m[13]! -
      m[12]! * m[1]! * m[6]! +
      m[12]! * m[2]! * m[5]!
    inv[3] =
      -m[1]! * m[6]! * m[11]! +
      m[1]! * m[7]! * m[10]! +
      m[5]! * m[2]! * m[11]! -
      m[5]! * m[3]! * m[10]! -
      m[9]! * m[2]! * m[7]! +
      m[9]! * m[3]! * m[6]!
    inv[7] =
      m[0]! * m[6]! * m[11]! -
      m[0]! * m[7]! * m[10]! -
      m[4]! * m[2]! * m[11]! +
      m[4]! * m[3]! * m[10]! +
      m[8]! * m[2]! * m[7]! -
      m[8]! * m[3]! * m[6]!
    inv[11] =
      -m[0]! * m[5]! * m[11]! +
      m[0]! * m[7]! * m[9]! +
      m[4]! * m[1]! * m[11]! -
      m[4]! * m[3]! * m[9]! -
      m[8]! * m[1]! * m[7]! +
      m[8]! * m[3]! * m[5]!
    inv[15] =
      m[0]! * m[5]! * m[10]! -
      m[0]! * m[6]! * m[9]! -
      m[4]! * m[1]! * m[10]! +
      m[4]! * m[2]! * m[9]! +
      m[8]! * m[1]! * m[6]! -
      m[8]! * m[2]! * m[5]!

    const det = m[0]! * inv[0]! + m[1]! * inv[4]! + m[2]! * inv[8]! + m[3]! * inv[12]!

    if (Math.abs(det) < 0.0001) {
      // Matrix is not invertible, set to identity
      this.setIdentity()
      return this
    }

    const invDet = 1.0 / det
    for (let i = 0; i < 16; i++) {
      inv[i]! *= invDet
    }

    this.data.set(inv)
    return this
  }

  /**
   * Return inverted matrix (this unchanged)
   */
  inverted(): Matrix4 {
    return this.clone().invert()
  }

  /**
   * Transpose this matrix in place
   */
  transpose(): this {
    const m = this.data
    let tmp: number

    tmp = m[1]!; m[1] = m[4]!; m[4] = tmp
    tmp = m[2]!; m[2] = m[8]!; m[8] = tmp
    tmp = m[3]!; m[3] = m[12]!; m[12] = tmp
    tmp = m[6]!; m[6] = m[9]!; m[9] = tmp
    tmp = m[7]!; m[7] = m[13]!; m[13] = tmp
    tmp = m[11]!; m[11] = m[14]!; m[14] = tmp

    return this
  }

  /**
   * Return transposed matrix (this unchanged)
   */
  transposed(): Matrix4 {
    return this.clone().transpose()
  }

  /**
   * Transform a point (x, y, z, w=1) by this matrix
   */
  transformPoint(x: number, y: number, z: number): { x: number; y: number; z: number } {
    const m = this.data
    const w = m[3]! * x + m[7]! * y + m[11]! * z + m[15]!

    return {
      x: (m[0]! * x + m[4]! * y + m[8]! * z + m[12]!) / w,
      y: (m[1]! * x + m[5]! * y + m[9]! * z + m[13]!) / w,
      z: (m[2]! * x + m[6]! * y + m[10]! * z + m[14]!) / w,
    }
  }

  /**
   * Transform a direction (x, y, z, w=0) by this matrix (ignores translation)
   */
  transformDirection(x: number, y: number, z: number): { x: number; y: number; z: number } {
    const m = this.data

    return {
      x: m[0]! * x + m[4]! * y + m[8]! * z,
      y: m[1]! * x + m[5]! * y + m[9]! * z,
      z: m[2]! * x + m[6]! * y + m[10]! * z,
    }
  }

  /**
   * Extract the upper-left 3x3 as a Float32Array (useful for normal matrix)
   */
  extractMatrix3(): Float32Array {
    const m = this.data
    return new Float32Array([
      m[0]!, m[1]!, m[2]!,
      m[4]!, m[5]!, m[6]!,
      m[8]!, m[9]!, m[10]!,
    ])
  }

  /**
   * Calculate determinant
   */
  determinant(): number {
    const m = this.data

    const inv0 =
      m[5]! * m[10]! * m[15]! -
      m[5]! * m[11]! * m[14]! -
      m[9]! * m[6]! * m[15]! +
      m[9]! * m[7]! * m[14]! +
      m[13]! * m[6]! * m[11]! -
      m[13]! * m[7]! * m[10]!

    const inv4 =
      -m[4]! * m[10]! * m[15]! +
      m[4]! * m[11]! * m[14]! +
      m[8]! * m[6]! * m[15]! -
      m[8]! * m[7]! * m[14]! -
      m[12]! * m[6]! * m[11]! +
      m[12]! * m[7]! * m[10]!

    const inv8 =
      m[4]! * m[9]! * m[15]! -
      m[4]! * m[11]! * m[13]! -
      m[8]! * m[5]! * m[15]! +
      m[8]! * m[7]! * m[13]! +
      m[12]! * m[5]! * m[11]! -
      m[12]! * m[7]! * m[9]!

    const inv12 =
      -m[4]! * m[9]! * m[14]! +
      m[4]! * m[10]! * m[13]! +
      m[8]! * m[5]! * m[14]! -
      m[8]! * m[6]! * m[13]! -
      m[12]! * m[5]! * m[10]! +
      m[12]! * m[6]! * m[9]!

    return m[0]! * inv0 + m[1]! * inv4 + m[2]! * inv8 + m[3]! * inv12
  }

  /**
   * Check if matrices are approximately equal
   */
  equals(other: Matrix4, epsilon = 0.0001): boolean {
    for (let i = 0; i < 16; i++) {
      if (Math.abs(this.data[i]! - other.data[i]!) > epsilon) {
        return false
      }
    }
    return true
  }

  /**
   * String representation
   */
  toString(): string {
    const m = this.data
    return `Matrix4(\n  ${m[0]?.toFixed(3)}, ${m[4]?.toFixed(3)}, ${m[8]?.toFixed(3)}, ${m[12]?.toFixed(3)}\n  ${m[1]?.toFixed(3)}, ${m[5]?.toFixed(3)}, ${m[9]?.toFixed(3)}, ${m[13]?.toFixed(3)}\n  ${m[2]?.toFixed(3)}, ${m[6]?.toFixed(3)}, ${m[10]?.toFixed(3)}, ${m[14]?.toFixed(3)}\n  ${m[3]?.toFixed(3)}, ${m[7]?.toFixed(3)}, ${m[11]?.toFixed(3)}, ${m[15]?.toFixed(3)}\n)`
  }
}
