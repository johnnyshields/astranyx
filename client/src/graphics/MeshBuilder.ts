/**
 * Fluent mesh building helper for procedural 3D geometry.
 * All meshes are arrays of triangles with position + normal data.
 */
export interface MeshData {
  vertices: Float32Array // Interleaved: x, y, z, nx, ny, nz
  vertexCount: number
}

/**
 * Helper class for building triangle meshes procedurally.
 * Supports automatic normal calculation.
 */
export class MeshBuilder {
  private vertices: number[] = []

  /**
   * Add a triangle with automatic normal calculation
   */
  addTriangle(
    x1: number,
    y1: number,
    z1: number,
    x2: number,
    y2: number,
    z2: number,
    x3: number,
    y3: number,
    z3: number
  ): this {
    // Calculate normal from cross product of edges
    const ux = x2 - x1,
      uy = y2 - y1,
      uz = z2 - z1
    const vx = x3 - x1,
      vy = y3 - y1,
      vz = z3 - z1
    let nx = uy * vz - uz * vy
    let ny = uz * vx - ux * vz
    let nz = ux * vy - uy * vx
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    if (len > 0) {
      nx /= len
      ny /= len
      nz /= len
    }

    this.vertices.push(x1, y1, z1, nx, ny, nz)
    this.vertices.push(x2, y2, z2, nx, ny, nz)
    this.vertices.push(x3, y3, z3, nx, ny, nz)

    return this
  }

  /**
   * Add a triangle with explicit normals
   */
  addTriangleWithNormals(
    x1: number, y1: number, z1: number, nx1: number, ny1: number, nz1: number,
    x2: number, y2: number, z2: number, nx2: number, ny2: number, nz2: number,
    x3: number, y3: number, z3: number, nx3: number, ny3: number, nz3: number
  ): this {
    this.vertices.push(x1, y1, z1, nx1, ny1, nz1)
    this.vertices.push(x2, y2, z2, nx2, ny2, nz2)
    this.vertices.push(x3, y3, z3, nx3, ny3, nz3)
    return this
  }

  /**
   * Add a quad (two triangles) with automatic normal calculation
   */
  addQuad(
    x1: number, y1: number, z1: number,
    x2: number, y2: number, z2: number,
    x3: number, y3: number, z3: number,
    x4: number, y4: number, z4: number
  ): this {
    // Quad vertices in order: 1, 2, 3, 4 (counter-clockwise)
    // First triangle: 1, 2, 3
    // Second triangle: 1, 3, 4
    this.addTriangle(x1, y1, z1, x2, y2, z2, x3, y3, z3)
    this.addTriangle(x1, y1, z1, x3, y3, z3, x4, y4, z4)
    return this
  }

  /**
   * Add a box centered at origin
   */
  addBox(width: number, height: number, depth: number): this {
    const hw = width / 2
    const hh = height / 2
    const hd = depth / 2

    // Front face (Z+)
    this.addTriangle(-hw, -hh, hd, hw, -hh, hd, hw, hh, hd)
    this.addTriangle(-hw, -hh, hd, hw, hh, hd, -hw, hh, hd)

    // Back face (Z-)
    this.addTriangle(hw, -hh, -hd, -hw, -hh, -hd, -hw, hh, -hd)
    this.addTriangle(hw, -hh, -hd, -hw, hh, -hd, hw, hh, -hd)

    // Top face (Y+)
    this.addTriangle(-hw, hh, hd, hw, hh, hd, hw, hh, -hd)
    this.addTriangle(-hw, hh, hd, hw, hh, -hd, -hw, hh, -hd)

    // Bottom face (Y-)
    this.addTriangle(-hw, -hh, -hd, hw, -hh, -hd, hw, -hh, hd)
    this.addTriangle(-hw, -hh, -hd, hw, -hh, hd, -hw, -hh, hd)

    // Right face (X+)
    this.addTriangle(hw, -hh, hd, hw, -hh, -hd, hw, hh, -hd)
    this.addTriangle(hw, -hh, hd, hw, hh, -hd, hw, hh, hd)

    // Left face (X-)
    this.addTriangle(-hw, -hh, -hd, -hw, -hh, hd, -hw, hh, hd)
    this.addTriangle(-hw, -hh, -hd, -hw, hh, hd, -hw, hh, -hd)

    return this
  }

  /**
   * Add a cylinder along the X axis
   */
  addCylinder(radius: number, length: number, segments: number = 8): this {
    const halfLen = length / 2

    for (let i = 0; i < segments; i++) {
      const a1 = (i / segments) * Math.PI * 2
      const a2 = ((i + 1) / segments) * Math.PI * 2
      const y1 = Math.cos(a1) * radius,
        z1 = Math.sin(a1) * radius
      const y2 = Math.cos(a2) * radius,
        z2 = Math.sin(a2) * radius

      // Side faces
      this.addTriangle(-halfLen, y1, z1, halfLen, y1, z1, halfLen, y2, z2)
      this.addTriangle(-halfLen, y1, z1, halfLen, y2, z2, -halfLen, y2, z2)

      // Front cap
      this.addTriangle(halfLen, 0, 0, halfLen, y1, z1, halfLen, y2, z2)

      // Back cap
      this.addTriangle(-halfLen, 0, 0, -halfLen, y2, z2, -halfLen, y1, z1)
    }

    return this
  }

  /**
   * Add a cone pointing along the X axis
   */
  addCone(radius: number, length: number, segments: number = 8): this {
    const tip = length

    for (let i = 0; i < segments; i++) {
      const a1 = (i / segments) * Math.PI * 2
      const a2 = ((i + 1) / segments) * Math.PI * 2
      const y1 = Math.cos(a1) * radius,
        z1 = Math.sin(a1) * radius
      const y2 = Math.cos(a2) * radius,
        z2 = Math.sin(a2) * radius

      // Side face
      this.addTriangle(0, y1, z1, tip, 0, 0, 0, y2, z2)

      // Base cap
      this.addTriangle(0, 0, 0, 0, y2, z2, 0, y1, z1)
    }

    return this
  }

  /**
   * Add an octahedron (diamond shape)
   */
  addOctahedron(radius: number): this {
    const top: [number, number, number] = [0, 0, radius]
    const bot: [number, number, number] = [0, 0, -radius]
    const front: [number, number, number] = [radius, 0, 0]
    const back: [number, number, number] = [-radius, 0, 0]
    const left: [number, number, number] = [0, radius, 0]
    const right: [number, number, number] = [0, -radius, 0]

    // Top pyramid
    this.addTriangle(...top, ...front, ...left)
    this.addTriangle(...top, ...left, ...back)
    this.addTriangle(...top, ...back, ...right)
    this.addTriangle(...top, ...right, ...front)

    // Bottom pyramid
    this.addTriangle(...bot, ...left, ...front)
    this.addTriangle(...bot, ...back, ...left)
    this.addTriangle(...bot, ...right, ...back)
    this.addTriangle(...bot, ...front, ...right)

    return this
  }

  /**
   * Add a pyramid (double pyramid / diamond shape)
   */
  addPyramid(radius: number, height: number): this {
    const top: [number, number, number] = [0, 0, height]
    const bot: [number, number, number] = [0, 0, -height]
    const corners: [number, number, number][] = [
      [radius, 0, 0],
      [0, radius, 0],
      [-radius, 0, 0],
      [0, -radius, 0],
    ]

    for (let i = 0; i < 4; i++) {
      const c1 = corners[i]!
      const c2 = corners[(i + 1) % 4]!
      // Top faces
      this.addTriangle(...top, ...c1, ...c2)
      // Bottom faces
      this.addTriangle(...bot, ...c2, ...c1)
    }

    return this
  }

  /**
   * Clear all vertices
   */
  clear(): this {
    this.vertices.length = 0
    return this
  }

  /**
   * Get current vertex count
   */
  getVertexCount(): number {
    return this.vertices.length / 6
  }

  /**
   * Build the final mesh data
   */
  build(): MeshData {
    return {
      vertices: new Float32Array(this.vertices),
      vertexCount: this.vertices.length / 6,
    }
  }
}
