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

// Generates a fighter jet style player ship mesh
// Oriented for side-scrolling: X = forward, Y = up/down (screen vertical), Z = depth (into screen)
export function createPlayerShipMesh(): MeshData {
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

  // Fighter jet proportions
  const nose = [0.5, 0, 0]

  // Cockpit area (raised canopy)
  const canopyFront = [0.15, 0.12, 0]
  const canopyPeak = [-0.05, 0.18, 0]
  const canopyBack = [-0.2, 0.1, 0]
  const canopyL = [-0.05, 0.1, 0.08]
  const canopyR = [-0.05, 0.1, -0.08]

  // Main fuselage (sleek body)
  const bodyFrontL = [0.1, 0, 0.1]
  const bodyFrontR = [0.1, 0, -0.1]
  const bodyMidL = [-0.15, 0, 0.12]
  const bodyMidR = [-0.15, 0, -0.12]
  const bodyBackL = [-0.4, 0, 0.08]
  const bodyBackR = [-0.4, 0, -0.08]

  // Underside
  const bellyFront = [0.1, -0.06, 0]
  const bellyMid = [-0.15, -0.08, 0]
  const bellyBack = [-0.4, -0.05, 0]

  // Tail
  const tailTop = [-0.5, 0.15, 0]
  const tailBot = [-0.5, -0.03, 0]
  const tailL = [-0.5, 0, 0.05]
  const tailR = [-0.5, 0, -0.05]

  // === NOSE CONE ===
  // Top nose surfaces
  addTri(nose[0]!, nose[1]!, nose[2]!, canopyFront[0]!, canopyFront[1]!, canopyFront[2]!, bodyFrontL[0]!, bodyFrontL[1]!, bodyFrontL[2]!)
  addTri(nose[0]!, nose[1]!, nose[2]!, bodyFrontR[0]!, bodyFrontR[1]!, bodyFrontR[2]!, canopyFront[0]!, canopyFront[1]!, canopyFront[2]!)
  // Bottom nose surfaces
  addTri(nose[0]!, nose[1]!, nose[2]!, bodyFrontL[0]!, bodyFrontL[1]!, bodyFrontL[2]!, bellyFront[0]!, bellyFront[1]!, bellyFront[2]!)
  addTri(nose[0]!, nose[1]!, nose[2]!, bellyFront[0]!, bellyFront[1]!, bellyFront[2]!, bodyFrontR[0]!, bodyFrontR[1]!, bodyFrontR[2]!)

  // === CANOPY (raised cockpit) ===
  addTri(canopyFront[0]!, canopyFront[1]!, canopyFront[2]!, canopyPeak[0]!, canopyPeak[1]!, canopyPeak[2]!, canopyL[0]!, canopyL[1]!, canopyL[2]!)
  addTri(canopyFront[0]!, canopyFront[1]!, canopyFront[2]!, canopyR[0]!, canopyR[1]!, canopyR[2]!, canopyPeak[0]!, canopyPeak[1]!, canopyPeak[2]!)
  addTri(canopyPeak[0]!, canopyPeak[1]!, canopyPeak[2]!, canopyBack[0]!, canopyBack[1]!, canopyBack[2]!, canopyL[0]!, canopyL[1]!, canopyL[2]!)
  addTri(canopyPeak[0]!, canopyPeak[1]!, canopyPeak[2]!, canopyR[0]!, canopyR[1]!, canopyR[2]!, canopyBack[0]!, canopyBack[1]!, canopyBack[2]!)

  // === MAIN BODY TOP ===
  // Front to mid
  addTri(canopyFront[0]!, canopyFront[1]!, canopyFront[2]!, canopyL[0]!, canopyL[1]!, canopyL[2]!, bodyFrontL[0]!, bodyFrontL[1]!, bodyFrontL[2]!)
  addTri(canopyFront[0]!, canopyFront[1]!, canopyFront[2]!, bodyFrontR[0]!, bodyFrontR[1]!, bodyFrontR[2]!, canopyR[0]!, canopyR[1]!, canopyR[2]!)
  addTri(canopyL[0]!, canopyL[1]!, canopyL[2]!, bodyMidL[0]!, bodyMidL[1]!, bodyMidL[2]!, bodyFrontL[0]!, bodyFrontL[1]!, bodyFrontL[2]!)
  addTri(canopyR[0]!, canopyR[1]!, canopyR[2]!, bodyFrontR[0]!, bodyFrontR[1]!, bodyFrontR[2]!, bodyMidR[0]!, bodyMidR[1]!, bodyMidR[2]!)
  // Mid to back
  addTri(canopyBack[0]!, canopyBack[1]!, canopyBack[2]!, bodyBackL[0]!, bodyBackL[1]!, bodyBackL[2]!, bodyMidL[0]!, bodyMidL[1]!, bodyMidL[2]!)
  addTri(canopyBack[0]!, canopyBack[1]!, canopyBack[2]!, bodyMidL[0]!, bodyMidL[1]!, bodyMidL[2]!, canopyL[0]!, canopyL[1]!, canopyL[2]!)
  addTri(canopyBack[0]!, canopyBack[1]!, canopyBack[2]!, bodyMidR[0]!, bodyMidR[1]!, bodyMidR[2]!, bodyBackR[0]!, bodyBackR[1]!, bodyBackR[2]!)
  addTri(canopyBack[0]!, canopyBack[1]!, canopyBack[2]!, canopyR[0]!, canopyR[1]!, canopyR[2]!, bodyMidR[0]!, bodyMidR[1]!, bodyMidR[2]!)

  // === UNDERSIDE ===
  addTri(bodyFrontL[0]!, bodyFrontL[1]!, bodyFrontL[2]!, bellyMid[0]!, bellyMid[1]!, bellyMid[2]!, bellyFront[0]!, bellyFront[1]!, bellyFront[2]!)
  addTri(bodyFrontL[0]!, bodyFrontL[1]!, bodyFrontL[2]!, bodyMidL[0]!, bodyMidL[1]!, bodyMidL[2]!, bellyMid[0]!, bellyMid[1]!, bellyMid[2]!)
  addTri(bodyFrontR[0]!, bodyFrontR[1]!, bodyFrontR[2]!, bellyFront[0]!, bellyFront[1]!, bellyFront[2]!, bellyMid[0]!, bellyMid[1]!, bellyMid[2]!)
  addTri(bodyFrontR[0]!, bodyFrontR[1]!, bodyFrontR[2]!, bellyMid[0]!, bellyMid[1]!, bellyMid[2]!, bodyMidR[0]!, bodyMidR[1]!, bodyMidR[2]!)
  addTri(bodyMidL[0]!, bodyMidL[1]!, bodyMidL[2]!, bellyBack[0]!, bellyBack[1]!, bellyBack[2]!, bellyMid[0]!, bellyMid[1]!, bellyMid[2]!)
  addTri(bodyMidL[0]!, bodyMidL[1]!, bodyMidL[2]!, bodyBackL[0]!, bodyBackL[1]!, bodyBackL[2]!, bellyBack[0]!, bellyBack[1]!, bellyBack[2]!)
  addTri(bodyMidR[0]!, bodyMidR[1]!, bodyMidR[2]!, bellyMid[0]!, bellyMid[1]!, bellyMid[2]!, bellyBack[0]!, bellyBack[1]!, bellyBack[2]!)
  addTri(bodyMidR[0]!, bodyMidR[1]!, bodyMidR[2]!, bellyBack[0]!, bellyBack[1]!, bellyBack[2]!, bodyBackR[0]!, bodyBackR[1]!, bodyBackR[2]!)

  // === TAIL SECTION ===
  // Top to tail
  addTri(canopyBack[0]!, canopyBack[1]!, canopyBack[2]!, tailTop[0]!, tailTop[1]!, tailTop[2]!, bodyBackL[0]!, bodyBackL[1]!, bodyBackL[2]!)
  addTri(canopyBack[0]!, canopyBack[1]!, canopyBack[2]!, bodyBackR[0]!, bodyBackR[1]!, bodyBackR[2]!, tailTop[0]!, tailTop[1]!, tailTop[2]!)
  // Sides to tail
  addTri(bodyBackL[0]!, bodyBackL[1]!, bodyBackL[2]!, tailTop[0]!, tailTop[1]!, tailTop[2]!, tailL[0]!, tailL[1]!, tailL[2]!)
  addTri(bodyBackR[0]!, bodyBackR[1]!, bodyBackR[2]!, tailR[0]!, tailR[1]!, tailR[2]!, tailTop[0]!, tailTop[1]!, tailTop[2]!)
  // Bottom to tail
  addTri(bodyBackL[0]!, bodyBackL[1]!, bodyBackL[2]!, tailL[0]!, tailL[1]!, tailL[2]!, bellyBack[0]!, bellyBack[1]!, bellyBack[2]!)
  addTri(bodyBackR[0]!, bodyBackR[1]!, bodyBackR[2]!, bellyBack[0]!, bellyBack[1]!, bellyBack[2]!, tailR[0]!, tailR[1]!, tailR[2]!)
  addTri(bellyBack[0]!, bellyBack[1]!, bellyBack[2]!, tailL[0]!, tailL[1]!, tailL[2]!, tailBot[0]!, tailBot[1]!, tailBot[2]!)
  addTri(bellyBack[0]!, bellyBack[1]!, bellyBack[2]!, tailBot[0]!, tailBot[1]!, tailBot[2]!, tailR[0]!, tailR[1]!, tailR[2]!)
  // Tail back face
  addTri(tailTop[0]!, tailTop[1]!, tailTop[2]!, tailR[0]!, tailR[1]!, tailR[2]!, tailL[0]!, tailL[1]!, tailL[2]!)
  addTri(tailBot[0]!, tailBot[1]!, tailBot[2]!, tailL[0]!, tailL[1]!, tailL[2]!, tailR[0]!, tailR[1]!, tailR[2]!)

  // === SWEPT WINGS ===
  const wingRoot = [-0.1, -0.02, 0.12]
  const wingTip = [-0.3, -0.02, 0.4]
  const wingBack = [-0.35, -0.02, 0.1]
  // Left wing top
  addTri(wingRoot[0]!, wingRoot[1]! + 0.02, wingRoot[2]!, wingTip[0]!, wingTip[1]! + 0.01, wingTip[2]!, wingBack[0]!, wingBack[1]! + 0.02, wingBack[2]!)
  // Left wing bottom
  addTri(wingRoot[0]!, wingRoot[1]!, wingRoot[2]!, wingBack[0]!, wingBack[1]!, wingBack[2]!, wingTip[0]!, wingTip[1]!, wingTip[2]!)

  // Right wing (mirror)
  const wingRootR = [-0.1, -0.02, -0.12]
  const wingTipR = [-0.3, -0.02, -0.4]
  const wingBackR = [-0.35, -0.02, -0.1]
  // Right wing top
  addTri(wingRootR[0]!, wingRootR[1]! + 0.02, wingRootR[2]!, wingBackR[0]!, wingBackR[1]! + 0.02, wingBackR[2]!, wingTipR[0]!, wingTipR[1]! + 0.01, wingTipR[2]!)
  // Right wing bottom
  addTri(wingRootR[0]!, wingRootR[1]!, wingRootR[2]!, wingTipR[0]!, wingTipR[1]!, wingTipR[2]!, wingBackR[0]!, wingBackR[1]!, wingBackR[2]!)

  // === VERTICAL TAIL FIN ===
  const finBase1 = [-0.35, 0.05, 0]
  const finBase2 = [-0.5, 0.05, 0]
  const finTip = [-0.48, 0.28, 0]
  // Both sides of fin
  addTri(finBase1[0]!, finBase1[1]!, finBase1[2]!, finTip[0]!, finTip[1]!, finTip[2]!, finBase2[0]!, finBase2[1]!, finBase2[2]!)
  addTri(finBase1[0]!, finBase1[1]!, finBase1[2]!, finBase2[0]!, finBase2[1]!, finBase2[2]!, finTip[0]!, finTip[1]!, finTip[2]!)

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
