// Procedural 3D mesh generation for 2.5D ships and enemies
// All meshes are arrays of triangles with position + normal data

export interface MeshData {
  vertices: Float32Array  // Interleaved: x, y, z, nx, ny, nz
  vertexCount: number
}

// Generates a basic box mesh
export function createBoxMesh(
  width: number,
  height: number,
  depth: number
): MeshData {
  const hw = width / 2
  const hh = height / 2
  const hd = depth / 2

  // 6 faces * 2 triangles * 3 vertices * 6 floats (pos + normal)
  const vertices = new Float32Array([
    // Front face (Z+)
    -hw, -hh,  hd,  0, 0, 1,
     hw, -hh,  hd,  0, 0, 1,
     hw,  hh,  hd,  0, 0, 1,
    -hw, -hh,  hd,  0, 0, 1,
     hw,  hh,  hd,  0, 0, 1,
    -hw,  hh,  hd,  0, 0, 1,

    // Back face (Z-)
     hw, -hh, -hd,  0, 0, -1,
    -hw, -hh, -hd,  0, 0, -1,
    -hw,  hh, -hd,  0, 0, -1,
     hw, -hh, -hd,  0, 0, -1,
    -hw,  hh, -hd,  0, 0, -1,
     hw,  hh, -hd,  0, 0, -1,

    // Top face (Y+)
    -hw,  hh,  hd,  0, 1, 0,
     hw,  hh,  hd,  0, 1, 0,
     hw,  hh, -hd,  0, 1, 0,
    -hw,  hh,  hd,  0, 1, 0,
     hw,  hh, -hd,  0, 1, 0,
    -hw,  hh, -hd,  0, 1, 0,

    // Bottom face (Y-)
    -hw, -hh, -hd,  0, -1, 0,
     hw, -hh, -hd,  0, -1, 0,
     hw, -hh,  hd,  0, -1, 0,
    -hw, -hh, -hd,  0, -1, 0,
     hw, -hh,  hd,  0, -1, 0,
    -hw, -hh,  hd,  0, -1, 0,

    // Right face (X+)
     hw, -hh,  hd,  1, 0, 0,
     hw, -hh, -hd,  1, 0, 0,
     hw,  hh, -hd,  1, 0, 0,
     hw, -hh,  hd,  1, 0, 0,
     hw,  hh, -hd,  1, 0, 0,
     hw,  hh,  hd,  1, 0, 0,

    // Left face (X-)
    -hw, -hh, -hd,  -1, 0, 0,
    -hw, -hh,  hd,  -1, 0, 0,
    -hw,  hh,  hd,  -1, 0, 0,
    -hw, -hh, -hd,  -1, 0, 0,
    -hw,  hh,  hd,  -1, 0, 0,
    -hw,  hh, -hd,  -1, 0, 0,
  ])

  return { vertices, vertexCount: 36 }
}

// Generates a wedge-shaped player ship mesh (pointed nose, flat back)
export function createPlayerShipMesh(): MeshData {
  // Ship dimensions
  const length = 1.0   // X length (nose to tail)
  const width = 0.6    // Y width (wingspan)
  const height = 0.25  // Z height (body depth)

  const vertices: number[] = []

  function addTri(
    x1: number, y1: number, z1: number,
    x2: number, y2: number, z2: number,
    x3: number, y3: number, z3: number
  ) {
    // Calculate normal
    const ux = x2 - x1, uy = y2 - y1, uz = z2 - z1
    const vx = x3 - x1, vy = y3 - y1, vz = z3 - z1
    let nx = uy * vz - uz * vy
    let ny = uz * vx - ux * vz
    let nz = ux * vy - uy * vx
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    if (len > 0) { nx /= len; ny /= len; nz /= len }

    vertices.push(x1, y1, z1, nx, ny, nz)
    vertices.push(x2, y2, z2, nx, ny, nz)
    vertices.push(x3, y3, z3, nx, ny, nz)
  }

  // Nose point
  const nose = [0.5, 0, 0]

  // Body vertices (back of ship)
  const backTop = [-0.5, 0, height / 2]
  const backBot = [-0.5, 0, -height / 2]
  const wingTopL = [-0.3, width / 2, height / 4]
  const wingTopR = [-0.3, -width / 2, height / 4]
  const wingBotL = [-0.3, width / 2, -height / 4]
  const wingBotR = [-0.3, -width / 2, -height / 4]

  // Top surface (2 triangles from nose to wings)
  addTri(nose[0]!, nose[1]!, nose[2]!, wingTopL[0]!, wingTopL[1]!, wingTopL[2]!, backTop[0]!, backTop[1]!, backTop[2]!)
  addTri(nose[0]!, nose[1]!, nose[2]!, backTop[0]!, backTop[1]!, backTop[2]!, wingTopR[0]!, wingTopR[1]!, wingTopR[2]!)

  // Bottom surface
  addTri(nose[0]!, nose[1]!, nose[2]!, backBot[0]!, backBot[1]!, backBot[2]!, wingBotL[0]!, wingBotL[1]!, wingBotL[2]!)
  addTri(nose[0]!, nose[1]!, nose[2]!, wingBotR[0]!, wingBotR[1]!, wingBotR[2]!, backBot[0]!, backBot[1]!, backBot[2]!)

  // Left side
  addTri(nose[0]!, nose[1]!, nose[2]!, wingBotL[0]!, wingBotL[1]!, wingBotL[2]!, wingTopL[0]!, wingTopL[1]!, wingTopL[2]!)

  // Right side
  addTri(nose[0]!, nose[1]!, nose[2]!, wingTopR[0]!, wingTopR[1]!, wingTopR[2]!, wingBotR[0]!, wingBotR[1]!, wingBotR[2]!)

  // Back face
  addTri(backTop[0]!, backTop[1]!, backTop[2]!, wingTopL[0]!, wingTopL[1]!, wingTopL[2]!, wingBotL[0]!, wingBotL[1]!, wingBotL[2]!)
  addTri(backTop[0]!, backTop[1]!, backTop[2]!, wingBotL[0]!, wingBotL[1]!, wingBotL[2]!, backBot[0]!, backBot[1]!, backBot[2]!)
  addTri(backTop[0]!, backTop[1]!, backTop[2]!, backBot[0]!, backBot[1]!, backBot[2]!, wingBotR[0]!, wingBotR[1]!, wingBotR[2]!)
  addTri(backTop[0]!, backTop[1]!, backTop[2]!, wingBotR[0]!, wingBotR[1]!, wingBotR[2]!, wingTopR[0]!, wingTopR[1]!, wingTopR[2]!)

  // Wing extensions (flat panels)
  const wingTipL = [-0.2, width * 0.8, 0]
  const wingTipR = [-0.2, -width * 0.8, 0]
  const wingBackL = [-0.5, width * 0.5, 0]
  const wingBackR = [-0.5, -width * 0.5, 0]

  // Left wing top
  addTri(wingTopL[0]!, wingTopL[1]!, wingTopL[2]!, wingTipL[0]!, wingTipL[1]!, wingTipL[2]!, wingBackL[0]!, wingBackL[1]!, wingBackL[2]!)
  // Left wing bottom
  addTri(wingBotL[0]!, wingBotL[1]!, wingBotL[2]!, wingBackL[0]!, wingBackL[1]!, wingBackL[2]!, wingTipL[0]!, wingTipL[1]!, wingTipL[2]!)

  // Right wing top
  addTri(wingTopR[0]!, wingTopR[1]!, wingTopR[2]!, wingBackR[0]!, wingBackR[1]!, wingBackR[2]!, wingTipR[0]!, wingTipR[1]!, wingTipR[2]!)
  // Right wing bottom
  addTri(wingBotR[0]!, wingBotR[1]!, wingBotR[2]!, wingTipR[0]!, wingTipR[1]!, wingTipR[2]!, wingBackR[0]!, wingBackR[1]!, wingBackR[2]!)

  return {
    vertices: new Float32Array(vertices),
    vertexCount: vertices.length / 6
  }
}

// Generates a basic enemy ship mesh (angular, menacing)
export function createEnemyShipMesh(): MeshData {
  const vertices: number[] = []

  function addTri(
    x1: number, y1: number, z1: number,
    x2: number, y2: number, z2: number,
    x3: number, y3: number, z3: number
  ) {
    const ux = x2 - x1, uy = y2 - y1, uz = z2 - z1
    const vx = x3 - x1, vy = y3 - y1, vz = z3 - z1
    let nx = uy * vz - uz * vy
    let ny = uz * vx - ux * vz
    let nz = ux * vy - uy * vx
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    if (len > 0) { nx /= len; ny /= len; nz /= len }

    vertices.push(x1, y1, z1, nx, ny, nz)
    vertices.push(x2, y2, z2, nx, ny, nz)
    vertices.push(x3, y3, z3, nx, ny, nz)
  }

  // Enemy faces left (negative X direction)
  // More angular/aggressive shape
  const nose = [-0.5, 0, 0]
  const topFront = [0.2, 0, 0.3]
  const topBack = [0.5, 0, 0.2]
  const botFront = [0.2, 0, -0.3]
  const botBack = [0.5, 0, -0.2]
  const wingTopL = [0.3, 0.5, 0.1]
  const wingTopR = [0.3, -0.5, 0.1]
  const wingBotL = [0.3, 0.5, -0.1]
  const wingBotR = [0.3, -0.5, -0.1]

  // Top hull
  addTri(nose[0]!, nose[1]!, nose[2]!, topFront[0]!, topFront[1]!, topFront[2]!, wingTopL[0]!, wingTopL[1]!, wingTopL[2]!)
  addTri(nose[0]!, nose[1]!, nose[2]!, wingTopR[0]!, wingTopR[1]!, wingTopR[2]!, topFront[0]!, topFront[1]!, topFront[2]!)
  addTri(topFront[0]!, topFront[1]!, topFront[2]!, topBack[0]!, topBack[1]!, topBack[2]!, wingTopL[0]!, wingTopL[1]!, wingTopL[2]!)
  addTri(topFront[0]!, topFront[1]!, topFront[2]!, wingTopR[0]!, wingTopR[1]!, wingTopR[2]!, topBack[0]!, topBack[1]!, topBack[2]!)

  // Bottom hull
  addTri(nose[0]!, nose[1]!, nose[2]!, wingBotL[0]!, wingBotL[1]!, wingBotL[2]!, botFront[0]!, botFront[1]!, botFront[2]!)
  addTri(nose[0]!, nose[1]!, nose[2]!, botFront[0]!, botFront[1]!, botFront[2]!, wingBotR[0]!, wingBotR[1]!, wingBotR[2]!)
  addTri(botFront[0]!, botFront[1]!, botFront[2]!, wingBotL[0]!, wingBotL[1]!, wingBotL[2]!, botBack[0]!, botBack[1]!, botBack[2]!)
  addTri(botFront[0]!, botFront[1]!, botFront[2]!, botBack[0]!, botBack[1]!, botBack[2]!, wingBotR[0]!, wingBotR[1]!, wingBotR[2]!)

  // Sides
  addTri(nose[0]!, nose[1]!, nose[2]!, topFront[0]!, topFront[1]!, topFront[2]!, botFront[0]!, botFront[1]!, botFront[2]!)
  addTri(topFront[0]!, topFront[1]!, topFront[2]!, topBack[0]!, topBack[1]!, topBack[2]!, botBack[0]!, botBack[1]!, botBack[2]!)
  addTri(topFront[0]!, topFront[1]!, topFront[2]!, botBack[0]!, botBack[1]!, botBack[2]!, botFront[0]!, botFront[1]!, botFront[2]!)

  // Back
  addTri(topBack[0]!, topBack[1]!, topBack[2]!, botBack[0]!, botBack[1]!, botBack[2]!, wingBotL[0]!, wingBotL[1]!, wingBotL[2]!)
  addTri(topBack[0]!, topBack[1]!, topBack[2]!, wingBotL[0]!, wingBotL[1]!, wingBotL[2]!, wingTopL[0]!, wingTopL[1]!, wingTopL[2]!)
  addTri(topBack[0]!, topBack[1]!, topBack[2]!, wingTopR[0]!, wingTopR[1]!, wingTopR[2]!, wingBotR[0]!, wingBotR[1]!, wingBotR[2]!)
  addTri(topBack[0]!, topBack[1]!, topBack[2]!, wingBotR[0]!, wingBotR[1]!, wingBotR[2]!, botBack[0]!, botBack[1]!, botBack[2]!)

  return {
    vertices: new Float32Array(vertices),
    vertexCount: vertices.length / 6
  }
}

// Creates a tank enemy mesh (boxy, armored)
export function createTankMesh(): MeshData {
  const vertices: number[] = []

  function addTri(
    x1: number, y1: number, z1: number,
    x2: number, y2: number, z2: number,
    x3: number, y3: number, z3: number
  ) {
    const ux = x2 - x1, uy = y2 - y1, uz = z2 - z1
    const vx = x3 - x1, vy = y3 - y1, vz = z3 - z1
    let nx = uy * vz - uz * vy
    let ny = uz * vx - ux * vz
    let nz = ux * vy - uy * vx
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    if (len > 0) { nx /= len; ny /= len; nz /= len }

    vertices.push(x1, y1, z1, nx, ny, nz)
    vertices.push(x2, y2, z2, nx, ny, nz)
    vertices.push(x3, y3, z3, nx, ny, nz)
  }

  // Main body (blocky)
  const w = 0.4, h = 0.3, d = 0.4

  // Front face
  addTri(-w, -h, d, w, -h, d, w, h, d)
  addTri(-w, -h, d, w, h, d, -w, h, d)
  // Back face
  addTri(w, -h, -d, -w, -h, -d, -w, h, -d)
  addTri(w, -h, -d, -w, h, -d, w, h, -d)
  // Top face
  addTri(-w, h, d, w, h, d, w, h, -d)
  addTri(-w, h, d, w, h, -d, -w, h, -d)
  // Bottom face
  addTri(-w, -h, -d, w, -h, -d, w, -h, d)
  addTri(-w, -h, -d, w, -h, d, -w, -h, d)
  // Right face
  addTri(w, -h, d, w, -h, -d, w, h, -d)
  addTri(w, -h, d, w, h, -d, w, h, d)
  // Left face
  addTri(-w, -h, -d, -w, -h, d, -w, h, d)
  addTri(-w, -h, -d, -w, h, d, -w, h, -d)

  // Turret on top (smaller box)
  const tw = 0.2, th = 0.15, td = 0.2
  const ty = h + th

  // Turret front
  addTri(-tw, h, td, tw, h, td, tw, ty, td)
  addTri(-tw, h, td, tw, ty, td, -tw, ty, td)
  // Turret back
  addTri(tw, h, -td, -tw, h, -td, -tw, ty, -td)
  addTri(tw, h, -td, -tw, ty, -td, tw, ty, -td)
  // Turret top
  addTri(-tw, ty, td, tw, ty, td, tw, ty, -td)
  addTri(-tw, ty, td, tw, ty, -td, -tw, ty, -td)
  // Turret right
  addTri(tw, h, td, tw, h, -td, tw, ty, -td)
  addTri(tw, h, td, tw, ty, -td, tw, ty, td)
  // Turret left
  addTri(-tw, h, -td, -tw, h, td, -tw, ty, td)
  addTri(-tw, h, -td, -tw, ty, td, -tw, ty, -td)

  return {
    vertices: new Float32Array(vertices),
    vertexCount: vertices.length / 6
  }
}

// Creates a boss core mesh (sphere-like with panels)
export function createBossCoreMesh(): MeshData {
  const vertices: number[] = []

  function addTri(
    x1: number, y1: number, z1: number,
    x2: number, y2: number, z2: number,
    x3: number, y3: number, z3: number
  ) {
    const ux = x2 - x1, uy = y2 - y1, uz = z2 - z1
    const vx = x3 - x1, vy = y3 - y1, vz = z3 - z1
    let nx = uy * vz - uz * vy
    let ny = uz * vx - ux * vz
    let nz = ux * vy - uy * vx
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    if (len > 0) { nx /= len; ny /= len; nz /= len }

    vertices.push(x1, y1, z1, nx, ny, nz)
    vertices.push(x2, y2, z2, nx, ny, nz)
    vertices.push(x3, y3, z3, nx, ny, nz)
  }

  // Octahedron-like boss core
  const r = 0.5
  const top = [0, 0, r]
  const bot = [0, 0, -r]
  const front = [r, 0, 0]
  const back = [-r, 0, 0]
  const left = [0, r, 0]
  const right = [0, -r, 0]

  // Top pyramid
  addTri(top[0]!, top[1]!, top[2]!, front[0]!, front[1]!, front[2]!, left[0]!, left[1]!, left[2]!)
  addTri(top[0]!, top[1]!, top[2]!, left[0]!, left[1]!, left[2]!, back[0]!, back[1]!, back[2]!)
  addTri(top[0]!, top[1]!, top[2]!, back[0]!, back[1]!, back[2]!, right[0]!, right[1]!, right[2]!)
  addTri(top[0]!, top[1]!, top[2]!, right[0]!, right[1]!, right[2]!, front[0]!, front[1]!, front[2]!)

  // Bottom pyramid
  addTri(bot[0]!, bot[1]!, bot[2]!, left[0]!, left[1]!, left[2]!, front[0]!, front[1]!, front[2]!)
  addTri(bot[0]!, bot[1]!, bot[2]!, back[0]!, back[1]!, back[2]!, left[0]!, left[1]!, left[2]!)
  addTri(bot[0]!, bot[1]!, bot[2]!, right[0]!, right[1]!, right[2]!, back[0]!, back[1]!, back[2]!)
  addTri(bot[0]!, bot[1]!, bot[2]!, front[0]!, front[1]!, front[2]!, right[0]!, right[1]!, right[2]!)

  return {
    vertices: new Float32Array(vertices),
    vertexCount: vertices.length / 6
  }
}

// Creates a drone mesh (small, spherical-ish)
export function createDroneMesh(): MeshData {
  // Smaller octahedron
  const vertices: number[] = []

  function addTri(
    x1: number, y1: number, z1: number,
    x2: number, y2: number, z2: number,
    x3: number, y3: number, z3: number
  ) {
    const ux = x2 - x1, uy = y2 - y1, uz = z2 - z1
    const vx = x3 - x1, vy = y3 - y1, vz = z3 - z1
    let nx = uy * vz - uz * vy
    let ny = uz * vx - ux * vz
    let nz = ux * vy - uy * vx
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    if (len > 0) { nx /= len; ny /= len; nz /= len }

    vertices.push(x1, y1, z1, nx, ny, nz)
    vertices.push(x2, y2, z2, nx, ny, nz)
    vertices.push(x3, y3, z3, nx, ny, nz)
  }

  const r = 0.4
  const top = [0, 0, r]
  const bot = [0, 0, -r]
  const front = [r, 0, 0]
  const back = [-r, 0, 0]
  const left = [0, r, 0]
  const right = [0, -r, 0]

  // Top pyramid
  addTri(top[0]!, top[1]!, top[2]!, front[0]!, front[1]!, front[2]!, left[0]!, left[1]!, left[2]!)
  addTri(top[0]!, top[1]!, top[2]!, left[0]!, left[1]!, left[2]!, back[0]!, back[1]!, back[2]!)
  addTri(top[0]!, top[1]!, top[2]!, back[0]!, back[1]!, back[2]!, right[0]!, right[1]!, right[2]!)
  addTri(top[0]!, top[1]!, top[2]!, right[0]!, right[1]!, right[2]!, front[0]!, front[1]!, front[2]!)

  // Bottom pyramid
  addTri(bot[0]!, bot[1]!, bot[2]!, left[0]!, left[1]!, left[2]!, front[0]!, front[1]!, front[2]!)
  addTri(bot[0]!, bot[1]!, bot[2]!, back[0]!, back[1]!, back[2]!, left[0]!, left[1]!, left[2]!)
  addTri(bot[0]!, bot[1]!, bot[2]!, right[0]!, right[1]!, right[2]!, back[0]!, back[1]!, back[2]!)
  addTri(bot[0]!, bot[1]!, bot[2]!, front[0]!, front[1]!, front[2]!, right[0]!, right[1]!, right[2]!)

  return {
    vertices: new Float32Array(vertices),
    vertexCount: vertices.length / 6
  }
}

// Creates an orb mesh (icosahedron approximation)
export function createOrbMesh(): MeshData {
  const vertices: number[] = []

  function addTri(
    x1: number, y1: number, z1: number,
    x2: number, y2: number, z2: number,
    x3: number, y3: number, z3: number
  ) {
    const ux = x2 - x1, uy = y2 - y1, uz = z2 - z1
    const vx = x3 - x1, vy = y3 - y1, vz = z3 - z1
    let nx = uy * vz - uz * vy
    let ny = uz * vx - ux * vz
    let nz = ux * vy - uy * vx
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    if (len > 0) { nx /= len; ny /= len; nz /= len }

    vertices.push(x1, y1, z1, nx, ny, nz)
    vertices.push(x2, y2, z2, nx, ny, nz)
    vertices.push(x3, y3, z3, nx, ny, nz)
  }

  // Icosahedron vertices
  const t = (1 + Math.sqrt(5)) / 2
  const r = 0.3

  const verts = [
    [-1, t, 0], [1, t, 0], [-1, -t, 0], [1, -t, 0],
    [0, -1, t], [0, 1, t], [0, -1, -t], [0, 1, -t],
    [t, 0, -1], [t, 0, 1], [-t, 0, -1], [-t, 0, 1]
  ].map(v => {
    const len = Math.sqrt(v[0]! * v[0]! + v[1]! * v[1]! + v[2]! * v[2]!)
    return [v[0]! / len * r, v[1]! / len * r, v[2]! / len * r]
  })

  const faces = [
    [0, 11, 5], [0, 5, 1], [0, 1, 7], [0, 7, 10], [0, 10, 11],
    [1, 5, 9], [5, 11, 4], [11, 10, 2], [10, 7, 6], [7, 1, 8],
    [3, 9, 4], [3, 4, 2], [3, 2, 6], [3, 6, 8], [3, 8, 9],
    [4, 9, 5], [2, 4, 11], [6, 2, 10], [8, 6, 7], [9, 8, 1]
  ]

  for (const face of faces) {
    const v0 = verts[face[0]!]!
    const v1 = verts[face[1]!]!
    const v2 = verts[face[2]!]!
    addTri(v0[0]!, v0[1]!, v0[2]!, v1[0]!, v1[1]!, v1[2]!, v2[0]!, v2[1]!, v2[2]!)
  }

  return {
    vertices: new Float32Array(vertices),
    vertexCount: vertices.length / 6
  }
}

// Creates a powerup mesh (spinning diamond)
export function createPowerupMesh(): MeshData {
  const vertices: number[] = []

  function addTri(
    x1: number, y1: number, z1: number,
    x2: number, y2: number, z2: number,
    x3: number, y3: number, z3: number
  ) {
    const ux = x2 - x1, uy = y2 - y1, uz = z2 - z1
    const vx = x3 - x1, vy = y3 - y1, vz = z3 - z1
    let nx = uy * vz - uz * vy
    let ny = uz * vx - ux * vz
    let nz = ux * vy - uy * vx
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    if (len > 0) { nx /= len; ny /= len; nz /= len }

    vertices.push(x1, y1, z1, nx, ny, nz)
    vertices.push(x2, y2, z2, nx, ny, nz)
    vertices.push(x3, y3, z3, nx, ny, nz)
  }

  // Diamond shape (double pyramid)
  const r = 0.4
  const h = 0.5

  const top = [0, 0, h]
  const bot = [0, 0, -h]
  const corners = [
    [r, 0, 0],
    [0, r, 0],
    [-r, 0, 0],
    [0, -r, 0]
  ]

  for (let i = 0; i < 4; i++) {
    const c1 = corners[i]!
    const c2 = corners[(i + 1) % 4]!
    // Top faces
    addTri(top[0]!, top[1]!, top[2]!, c1[0]!, c1[1]!, c1[2]!, c2[0]!, c2[1]!, c2[2]!)
    // Bottom faces
    addTri(bot[0]!, bot[1]!, bot[2]!, c2[0]!, c2[1]!, c2[2]!, c1[0]!, c1[1]!, c1[2]!)
  }

  return {
    vertices: new Float32Array(vertices),
    vertexCount: vertices.length / 6
  }
}

// Create a mine mesh (spiky sphere)
export function createMineMesh(): MeshData {
  // Start with octahedron core, add spikes
  const vertices: number[] = []

  function addTri(
    x1: number, y1: number, z1: number,
    x2: number, y2: number, z2: number,
    x3: number, y3: number, z3: number
  ) {
    const ux = x2 - x1, uy = y2 - y1, uz = z2 - z1
    const vx = x3 - x1, vy = y3 - y1, vz = z3 - z1
    let nx = uy * vz - uz * vy
    let ny = uz * vx - ux * vz
    let nz = ux * vy - uy * vx
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    if (len > 0) { nx /= len; ny /= len; nz /= len }

    vertices.push(x1, y1, z1, nx, ny, nz)
    vertices.push(x2, y2, z2, nx, ny, nz)
    vertices.push(x3, y3, z3, nx, ny, nz)
  }

  // Core octahedron
  const r = 0.3
  const sr = 0.5 // spike radius

  const dirs = [
    [1, 0, 0], [-1, 0, 0],
    [0, 1, 0], [0, -1, 0],
    [0, 0, 1], [0, 0, -1]
  ]

  // Add spikes
  const spikeW = 0.1
  for (const dir of dirs) {
    const tip = [dir[0]! * sr, dir[1]! * sr, dir[2]! * sr]
    // Find perpendicular vectors
    let perp1: number[], perp2: number[]
    if (Math.abs(dir[0]!) > 0.9) {
      perp1 = [0, spikeW, 0]
      perp2 = [0, 0, spikeW]
    } else if (Math.abs(dir[1]!) > 0.9) {
      perp1 = [spikeW, 0, 0]
      perp2 = [0, 0, spikeW]
    } else {
      perp1 = [spikeW, 0, 0]
      perp2 = [0, spikeW, 0]
    }

    const base = [dir[0]! * r, dir[1]! * r, dir[2]! * r]

    // Four triangular faces per spike
    const b1 = [base[0]! + perp1[0]!, base[1]! + perp1[1]!, base[2]! + perp1[2]!]
    const b2 = [base[0]! + perp2[0]!, base[1]! + perp2[1]!, base[2]! + perp2[2]!]
    const b3 = [base[0]! - perp1[0]!, base[1]! - perp1[1]!, base[2]! - perp1[2]!]
    const b4 = [base[0]! - perp2[0]!, base[1]! - perp2[1]!, base[2]! - perp2[2]!]

    addTri(tip[0]!, tip[1]!, tip[2]!, b1[0]!, b1[1]!, b1[2]!, b2[0]!, b2[1]!, b2[2]!)
    addTri(tip[0]!, tip[1]!, tip[2]!, b2[0]!, b2[1]!, b2[2]!, b3[0]!, b3[1]!, b3[2]!)
    addTri(tip[0]!, tip[1]!, tip[2]!, b3[0]!, b3[1]!, b3[2]!, b4[0]!, b4[1]!, b4[2]!)
    addTri(tip[0]!, tip[1]!, tip[2]!, b4[0]!, b4[1]!, b4[2]!, b1[0]!, b1[1]!, b1[2]!)
  }

  return {
    vertices: new Float32Array(vertices),
    vertexCount: vertices.length / 6
  }
}
