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

// ============================================================
// WEAPON MESHES (16 types)
// All weapons oriented with barrel pointing +X (right)
// Scale: ~0.3-0.5 units long for attachment to ships
// ============================================================

// Helper to add triangles for weapon meshes
function createWeaponAddTri(vertices: number[]) {
  return function addTri(
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
}

// BULLET WEAPONS

// Vulcan - Minigun with rotating barrel cluster
export function createVulcanMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  // Main housing (hexagonal cylinder)
  const len = 0.4
  const r = 0.08
  const barrelCount = 6
  const barrelR = 0.025
  const barrelLen = 0.5

  // Housing body
  for (let i = 0; i < 6; i++) {
    const a1 = (i / 6) * Math.PI * 2
    const a2 = ((i + 1) / 6) * Math.PI * 2
    const x1 = Math.cos(a1) * r, z1 = Math.sin(a1) * r
    const x2 = Math.cos(a2) * r, z2 = Math.sin(a2) * r

    // Front cap
    addTri(0, 0, 0, z1, x1, 0, z2, x2, 0)
    // Back cap
    addTri(-len, 0, 0, -len + z2, x2, 0, -len + z1, x1, 0)
    // Side
    addTri(z1, x1, 0, z1, x1, -len, z2, x2, -len)
    addTri(z1, x1, 0, z2, x2, -len, z2, x2, 0)
  }

  // Barrel cluster (6 barrels around center)
  for (let b = 0; b < barrelCount; b++) {
    const angle = (b / barrelCount) * Math.PI * 2
    const bx = Math.cos(angle) * 0.05
    const bz = Math.sin(angle) * 0.05

    // Each barrel as 4-sided tube
    for (let i = 0; i < 4; i++) {
      const a1 = (i / 4) * Math.PI * 2
      const a2 = ((i + 1) / 4) * Math.PI * 2
      const dx1 = Math.cos(a1) * barrelR, dz1 = Math.sin(a1) * barrelR
      const dx2 = Math.cos(a2) * barrelR, dz2 = Math.sin(a2) * barrelR

      // Barrel side
      addTri(bx + dx1, bz + dz1, 0, bx + dx1, bz + dz1, barrelLen, bx + dx2, bz + dz2, barrelLen)
      addTri(bx + dx1, bz + dz1, 0, bx + dx2, bz + dz2, barrelLen, bx + dx2, bz + dz2, 0)
    }
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Shotgun (Bulldog) - Wide double barrel
export function createShotgunMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.35
  const barrelR = 0.04
  const barrelSep = 0.06

  // Two barrels
  for (const offset of [-barrelSep / 2, barrelSep / 2]) {
    for (let i = 0; i < 6; i++) {
      const a1 = (i / 6) * Math.PI * 2
      const a2 = ((i + 1) / 6) * Math.PI * 2
      const dx1 = Math.cos(a1) * barrelR, dy1 = Math.sin(a1) * barrelR
      const dx2 = Math.cos(a2) * barrelR, dy2 = Math.sin(a2) * barrelR

      // Barrel side
      addTri(len, offset + dy1, dx1, 0, offset + dy1, dx1, 0, offset + dy2, dx2)
      addTri(len, offset + dy1, dx1, 0, offset + dy2, dx2, len, offset + dy2, dx2)
      // Front cap
      addTri(len, offset, 0, len, offset + dy1, dx1, len, offset + dy2, dx2)
    }
  }

  // Stock/grip
  const sw = 0.05, sh = 0.1, sd = 0.12
  addTri(-sd, -sh, -sw, -sd, -sh, sw, 0, -sh, sw)
  addTri(-sd, -sh, -sw, 0, -sh, sw, 0, -sh, -sw)
  addTri(-sd, 0, -sw, -sd, -sh, -sw, 0, -sh, -sw)
  addTri(-sd, 0, -sw, 0, -sh, -sw, 0, 0, -sw)
  addTri(-sd, 0, sw, 0, 0, sw, 0, -sh, sw)
  addTri(-sd, 0, sw, 0, -sh, sw, -sd, -sh, sw)

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Spread Small (Jericho) - 5-way spread gun
export function createSpreadSmallMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.3
  const bodyW = 0.1, bodyH = 0.06

  // Main body (flat box)
  addTri(len, -bodyH, -bodyW, len, -bodyH, bodyW, len, bodyH, bodyW)
  addTri(len, -bodyH, -bodyW, len, bodyH, bodyW, len, bodyH, -bodyW)
  addTri(0, -bodyH, -bodyW, 0, bodyH, -bodyW, 0, bodyH, bodyW)
  addTri(0, -bodyH, -bodyW, 0, bodyH, bodyW, 0, -bodyH, bodyW)
  addTri(0, bodyH, -bodyW, len, bodyH, -bodyW, len, bodyH, bodyW)
  addTri(0, bodyH, -bodyW, len, bodyH, bodyW, 0, bodyH, bodyW)
  addTri(0, -bodyH, bodyW, len, -bodyH, bodyW, len, -bodyH, -bodyW)
  addTri(0, -bodyH, bodyW, len, -bodyH, -bodyW, 0, -bodyH, -bodyW)
  addTri(0, -bodyH, -bodyW, len, -bodyH, -bodyW, len, bodyH, -bodyW)
  addTri(0, -bodyH, -bodyW, len, bodyH, -bodyW, 0, bodyH, -bodyW)
  addTri(len, -bodyH, bodyW, 0, -bodyH, bodyW, 0, bodyH, bodyW)
  addTri(len, -bodyH, bodyW, 0, bodyH, bodyW, len, bodyH, bodyW)

  // 5 barrel nubs
  const nubR = 0.015, nubLen = 0.05
  for (let i = -2; i <= 2; i++) {
    const nubZ = i * 0.035
    for (let j = 0; j < 4; j++) {
      const a1 = (j / 4) * Math.PI * 2
      const a2 = ((j + 1) / 4) * Math.PI * 2
      const dy1 = Math.cos(a1) * nubR, dz1 = Math.sin(a1) * nubR
      const dy2 = Math.cos(a2) * nubR, dz2 = Math.sin(a2) * nubR
      addTri(len, dy1, nubZ + dz1, len + nubLen, dy1, nubZ + dz1, len + nubLen, dy2, nubZ + dz2)
      addTri(len, dy1, nubZ + dz1, len + nubLen, dy2, nubZ + dz2, len, dy2, nubZ + dz2)
    }
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Spread Large (Kitsune) - 9-way spread (wider variant)
export function createSpreadLargeMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.32
  const bodyW = 0.15, bodyH = 0.05

  // Main body (wider, flatter)
  addTri(len, -bodyH, -bodyW, len, -bodyH, bodyW, len, bodyH, bodyW)
  addTri(len, -bodyH, -bodyW, len, bodyH, bodyW, len, bodyH, -bodyW)
  addTri(0, -bodyH, -bodyW, 0, bodyH, -bodyW, 0, bodyH, bodyW)
  addTri(0, -bodyH, -bodyW, 0, bodyH, bodyW, 0, -bodyH, bodyW)
  addTri(0, bodyH, -bodyW, len, bodyH, -bodyW, len, bodyH, bodyW)
  addTri(0, bodyH, -bodyW, len, bodyH, bodyW, 0, bodyH, bodyW)
  addTri(0, -bodyH, bodyW, len, -bodyH, bodyW, len, -bodyH, -bodyW)
  addTri(0, -bodyH, bodyW, len, -bodyH, -bodyW, 0, -bodyH, -bodyW)

  // Fan-shaped front plate
  const fanR = 0.18
  for (let i = 0; i < 8; i++) {
    const a1 = (i / 8 - 0.5) * Math.PI * 0.6
    const a2 = ((i + 1) / 8 - 0.5) * Math.PI * 0.6
    addTri(len, 0, 0, len + 0.03, Math.sin(a1) * 0.02, Math.cos(a1) * fanR, len + 0.03, Math.sin(a2) * 0.02, Math.cos(a2) * fanR)
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Railgun (Odin) - Long piercing barrel
export function createRailgunMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.6
  const bodyR = 0.04
  const barrelR = 0.02, barrelLen = 0.55

  // Main housing (octagonal)
  for (let i = 0; i < 8; i++) {
    const a1 = (i / 8) * Math.PI * 2
    const a2 = ((i + 1) / 8) * Math.PI * 2
    const dy1 = Math.cos(a1) * bodyR, dz1 = Math.sin(a1) * bodyR
    const dy2 = Math.cos(a2) * bodyR, dz2 = Math.sin(a2) * bodyR

    addTri(0, dy1, dz1, len * 0.3, dy1, dz1, len * 0.3, dy2, dz2)
    addTri(0, dy1, dz1, len * 0.3, dy2, dz2, 0, dy2, dz2)
  }

  // Long thin barrel with rails
  for (let i = 0; i < 4; i++) {
    const a1 = (i / 4) * Math.PI * 2
    const a2 = ((i + 1) / 4) * Math.PI * 2
    const dy1 = Math.cos(a1) * barrelR, dz1 = Math.sin(a1) * barrelR
    const dy2 = Math.cos(a2) * barrelR, dz2 = Math.sin(a2) * barrelR

    addTri(len * 0.2, dy1, dz1, barrelLen, dy1, dz1, barrelLen, dy2, dz2)
    addTri(len * 0.2, dy1, dz1, barrelLen, dy2, dz2, len * 0.2, dy2, dz2)
  }

  // Rail fins (2 parallel rails)
  const railH = 0.06, railW = 0.01
  for (const side of [-1, 1]) {
    addTri(0.1, 0, side * 0.03, 0.5, railH, side * (0.03 + railW), 0.5, 0, side * 0.03)
    addTri(0.1, 0, side * 0.03, 0.1, railH, side * (0.03 + railW), 0.5, railH, side * (0.03 + railW))
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// BOMB WEAPONS

// Missile (Hornet) - Torpedo launcher
export function createMissileMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.35
  const tubeR = 0.05

  // Launch tube (hexagonal)
  for (let i = 0; i < 6; i++) {
    const a1 = (i / 6) * Math.PI * 2
    const a2 = ((i + 1) / 6) * Math.PI * 2
    const dy1 = Math.cos(a1) * tubeR, dz1 = Math.sin(a1) * tubeR
    const dy2 = Math.cos(a2) * tubeR, dz2 = Math.sin(a2) * tubeR

    addTri(0, dy1, dz1, len, dy1, dz1, len, dy2, dz2)
    addTri(0, dy1, dz1, len, dy2, dz2, 0, dy2, dz2)
    // Back cap
    addTri(0, 0, 0, 0, dy2, dz2, 0, dy1, dz1)
  }

  // Missile visible inside (smaller cylinder + cone)
  const missileR = 0.03
  for (let i = 0; i < 4; i++) {
    const a1 = (i / 4) * Math.PI * 2
    const a2 = ((i + 1) / 4) * Math.PI * 2
    const dy1 = Math.cos(a1) * missileR, dz1 = Math.sin(a1) * missileR
    const dy2 = Math.cos(a2) * missileR, dz2 = Math.sin(a2) * missileR

    addTri(0.05, dy1, dz1, len - 0.05, dy1, dz1, len - 0.05, dy2, dz2)
    addTri(0.05, dy1, dz1, len - 0.05, dy2, dz2, 0.05, dy2, dz2)
    // Cone tip
    addTri(len - 0.05, dy1, dz1, len + 0.02, 0, 0, len - 0.05, dy2, dz2)
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Cannon (Megiddo) - Heavy explosive cannon
export function createCannonMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.4
  const baseR = 0.07, barrelR = 0.045

  // Chunky base
  for (let i = 0; i < 8; i++) {
    const a1 = (i / 8) * Math.PI * 2
    const a2 = ((i + 1) / 8) * Math.PI * 2
    const dy1 = Math.cos(a1) * baseR, dz1 = Math.sin(a1) * baseR
    const dy2 = Math.cos(a2) * baseR, dz2 = Math.sin(a2) * baseR

    addTri(0, dy1, dz1, len * 0.4, dy1, dz1, len * 0.4, dy2, dz2)
    addTri(0, dy1, dz1, len * 0.4, dy2, dz2, 0, dy2, dz2)
    addTri(0, 0, 0, 0, dy2, dz2, 0, dy1, dz1)
  }

  // Barrel with flared end
  for (let i = 0; i < 6; i++) {
    const a1 = (i / 6) * Math.PI * 2
    const a2 = ((i + 1) / 6) * Math.PI * 2
    const dy1 = Math.cos(a1) * barrelR, dz1 = Math.sin(a1) * barrelR
    const dy2 = Math.cos(a2) * barrelR, dz2 = Math.sin(a2) * barrelR
    const fy1 = Math.cos(a1) * barrelR * 1.3, fz1 = Math.sin(a1) * barrelR * 1.3
    const fy2 = Math.cos(a2) * barrelR * 1.3, fz2 = Math.sin(a2) * barrelR * 1.3

    addTri(len * 0.35, dy1, dz1, len * 0.9, dy1, dz1, len * 0.9, dy2, dz2)
    addTri(len * 0.35, dy1, dz1, len * 0.9, dy2, dz2, len * 0.35, dy2, dz2)
    // Flared muzzle
    addTri(len * 0.9, dy1, dz1, len, fy1, fz1, len, fy2, fz2)
    addTri(len * 0.9, dy1, dz1, len, fy2, fz2, len * 0.9, dy2, dz2)
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Limpet Mine launcher
export function createLimpetMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.3
  const boxW = 0.08, boxH = 0.06

  // Box launcher body
  addTri(len, -boxH, -boxW, len, boxH, -boxW, len, boxH, boxW)
  addTri(len, -boxH, -boxW, len, boxH, boxW, len, -boxH, boxW)
  addTri(0, -boxH, -boxW, 0, -boxH, boxW, 0, boxH, boxW)
  addTri(0, -boxH, -boxW, 0, boxH, boxW, 0, boxH, -boxW)
  addTri(0, boxH, -boxW, 0, boxH, boxW, len, boxH, boxW)
  addTri(0, boxH, -boxW, len, boxH, boxW, len, boxH, -boxW)
  addTri(0, -boxH, -boxW, len, -boxH, -boxW, len, -boxH, boxW)
  addTri(0, -boxH, -boxW, len, -boxH, boxW, 0, -boxH, boxW)

  // Mine visible in chamber (small spiky sphere)
  const mineR = 0.04
  const cx = len * 0.5
  for (const dir of [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]] as const) {
    const tipX = cx + dir[0] * mineR * 1.5
    const tipY = dir[1] * mineR * 1.5
    const tipZ = dir[2] * mineR * 1.5
    const baseX = cx + dir[0] * mineR * 0.5
    const baseY = dir[1] * mineR * 0.5
    const baseZ = dir[2] * mineR * 0.5
    const s = 0.015
    addTri(tipX, tipY, tipZ, baseX + s, baseY, baseZ, baseX, baseY + s, baseZ)
    addTri(tipX, tipY, tipZ, baseX, baseY + s, baseZ, baseX - s, baseY, baseZ)
    addTri(tipX, tipY, tipZ, baseX - s, baseY, baseZ, baseX, baseY - s, baseZ)
    addTri(tipX, tipY, tipZ, baseX, baseY - s, baseZ, baseX + s, baseY, baseZ)
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Grenade (Magus) - Grenade launcher
export function createGrenadeMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.35
  const drumR = 0.06

  // Drum magazine (cylinder)
  for (let i = 0; i < 8; i++) {
    const a1 = (i / 8) * Math.PI * 2
    const a2 = ((i + 1) / 8) * Math.PI * 2
    const dy1 = Math.cos(a1) * drumR, dz1 = Math.sin(a1) * drumR
    const dy2 = Math.cos(a2) * drumR, dz2 = Math.sin(a2) * drumR

    addTri(0.05, dy1 - 0.03, dz1, 0.2, dy1 - 0.03, dz1, 0.2, dy2 - 0.03, dz2)
    addTri(0.05, dy1 - 0.03, dz1, 0.2, dy2 - 0.03, dz2, 0.05, dy2 - 0.03, dz2)
  }

  // Barrel
  const barrelR = 0.035
  for (let i = 0; i < 6; i++) {
    const a1 = (i / 6) * Math.PI * 2
    const a2 = ((i + 1) / 6) * Math.PI * 2
    const dy1 = Math.cos(a1) * barrelR, dz1 = Math.sin(a1) * barrelR
    const dy2 = Math.cos(a2) * barrelR, dz2 = Math.sin(a2) * barrelR

    addTri(0.15, dy1, dz1, len, dy1, dz1, len, dy2, dz2)
    addTri(0.15, dy1, dz1, len, dy2, dz2, 0.15, dy2, dz2)
  }

  // Stock
  addTri(0, 0.02, -0.02, 0, 0.02, 0.02, 0, -0.06, 0.02)
  addTri(0, 0.02, -0.02, 0, -0.06, 0.02, 0, -0.06, -0.02)

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// OIL WEAPONS

// Flamethrower (Diablo)
export function createFlameMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.4
  const tankR = 0.05
  const nozzleR = 0.04

  // Fuel tank (cylinder, mounted under)
  for (let i = 0; i < 6; i++) {
    const a1 = (i / 6) * Math.PI * 2
    const a2 = ((i + 1) / 6) * Math.PI * 2
    const dy1 = Math.cos(a1) * tankR, dz1 = Math.sin(a1) * tankR
    const dy2 = Math.cos(a2) * tankR, dz2 = Math.sin(a2) * tankR

    addTri(0, dy1 - 0.06, dz1, 0.25, dy1 - 0.06, dz1, 0.25, dy2 - 0.06, dz2)
    addTri(0, dy1 - 0.06, dz1, 0.25, dy2 - 0.06, dz2, 0, dy2 - 0.06, dz2)
  }

  // Nozzle (cone flaring out)
  for (let i = 0; i < 6; i++) {
    const a1 = (i / 6) * Math.PI * 2
    const a2 = ((i + 1) / 6) * Math.PI * 2
    const dy1 = Math.cos(a1) * nozzleR * 0.5, dz1 = Math.sin(a1) * nozzleR * 0.5
    const dy2 = Math.cos(a2) * nozzleR * 0.5, dz2 = Math.sin(a2) * nozzleR * 0.5
    const fy1 = Math.cos(a1) * nozzleR * 1.5, fz1 = Math.sin(a1) * nozzleR * 1.5
    const fy2 = Math.cos(a2) * nozzleR * 1.5, fz2 = Math.sin(a2) * nozzleR * 1.5

    addTri(0.1, dy1, dz1, len - 0.05, dy1, dz1, len - 0.05, dy2, dz2)
    addTri(0.1, dy1, dz1, len - 0.05, dy2, dz2, 0.1, dy2, dz2)
    // Flared end
    addTri(len - 0.05, dy1, dz1, len, fy1, fz1, len, fy2, fz2)
    addTri(len - 0.05, dy1, dz1, len, fy2, fz2, len - 0.05, dy2, dz2)
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Acid (Slag) - Caustic sprayer
export function createAcidMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.35
  const canisterR = 0.045

  // Main canister body
  for (let i = 0; i < 6; i++) {
    const a1 = (i / 6) * Math.PI * 2
    const a2 = ((i + 1) / 6) * Math.PI * 2
    const dy1 = Math.cos(a1) * canisterR, dz1 = Math.sin(a1) * canisterR
    const dy2 = Math.cos(a2) * canisterR, dz2 = Math.sin(a2) * canisterR

    addTri(0, dy1, dz1, len * 0.7, dy1, dz1, len * 0.7, dy2, dz2)
    addTri(0, dy1, dz1, len * 0.7, dy2, dz2, 0, dy2, dz2)
    addTri(0, 0, 0, 0, dy2, dz2, 0, dy1, dz1)
  }

  // Nozzle with drip tip
  const nozzleR = 0.025
  for (let i = 0; i < 4; i++) {
    const a1 = (i / 4) * Math.PI * 2
    const a2 = ((i + 1) / 4) * Math.PI * 2
    const dy1 = Math.cos(a1) * nozzleR, dz1 = Math.sin(a1) * nozzleR
    const dy2 = Math.cos(a2) * nozzleR, dz2 = Math.sin(a2) * nozzleR

    addTri(len * 0.6, dy1, dz1, len, dy1, dz1, len, dy2, dz2)
    addTri(len * 0.6, dy1, dz1, len, dy2, dz2, len * 0.6, dy2, dz2)
  }

  // Drip (pyramid pointing down)
  addTri(len, 0.015, 0, len + 0.02, -0.03, 0, len, -0.015, 0.015)
  addTri(len, 0.015, 0, len, -0.015, -0.015, len + 0.02, -0.03, 0)

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// ENERGY WEAPONS

// Sonic (Banshee) - Wave emitter
export function createSonicMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.35

  // Main body (tapered)
  const backR = 0.06, frontR = 0.04
  for (let i = 0; i < 6; i++) {
    const a1 = (i / 6) * Math.PI * 2
    const a2 = ((i + 1) / 6) * Math.PI * 2
    const bdy1 = Math.cos(a1) * backR, bdz1 = Math.sin(a1) * backR
    const bdy2 = Math.cos(a2) * backR, bdz2 = Math.sin(a2) * backR
    const fdy1 = Math.cos(a1) * frontR, fdz1 = Math.sin(a1) * frontR
    const fdy2 = Math.cos(a2) * frontR, fdz2 = Math.sin(a2) * frontR

    addTri(0, bdy1, bdz1, len * 0.7, fdy1, fdz1, len * 0.7, fdy2, fdz2)
    addTri(0, bdy1, bdz1, len * 0.7, fdy2, fdz2, 0, bdy2, bdz2)
  }

  // Dish/horn (cone opening)
  const dishR = 0.08
  for (let i = 0; i < 8; i++) {
    const a1 = (i / 8) * Math.PI * 2
    const a2 = ((i + 1) / 8) * Math.PI * 2
    const dy1 = Math.cos(a1) * frontR, dz1 = Math.sin(a1) * frontR
    const dy2 = Math.cos(a2) * frontR, dz2 = Math.sin(a2) * frontR
    const ody1 = Math.cos(a1) * dishR, odz1 = Math.sin(a1) * dishR
    const ody2 = Math.cos(a2) * dishR, odz2 = Math.sin(a2) * dishR

    addTri(len * 0.7, dy1, dz1, len, ody1, odz1, len, ody2, odz2)
    addTri(len * 0.7, dy1, dz1, len, ody2, odz2, len * 0.7, dy2, dz2)
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Laser Small (Lancet) - Thin piercing laser
export function createLaserSmallMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.45
  const bodyR = 0.03

  // Sleek tapered body
  for (let i = 0; i < 4; i++) {
    const a1 = (i / 4) * Math.PI * 2
    const a2 = ((i + 1) / 4) * Math.PI * 2
    const dy1 = Math.cos(a1) * bodyR, dz1 = Math.sin(a1) * bodyR
    const dy2 = Math.cos(a2) * bodyR, dz2 = Math.sin(a2) * bodyR
    const tdy1 = Math.cos(a1) * bodyR * 0.3, tdz1 = Math.sin(a1) * bodyR * 0.3
    const tdy2 = Math.cos(a2) * bodyR * 0.3, tdz2 = Math.sin(a2) * bodyR * 0.3

    addTri(0, dy1, dz1, len * 0.6, dy1, dz1, len * 0.6, dy2, dz2)
    addTri(0, dy1, dz1, len * 0.6, dy2, dz2, 0, dy2, dz2)
    // Tapered front
    addTri(len * 0.6, dy1, dz1, len, tdy1, tdz1, len, tdy2, tdz2)
    addTri(len * 0.6, dy1, dz1, len, tdy2, tdz2, len * 0.6, dy2, dz2)
  }

  // Focus crystal at tip (small diamond)
  const cr = 0.015
  addTri(len, 0, 0, len - 0.02, cr, 0, len - 0.02, 0, cr)
  addTri(len, 0, 0, len - 0.02, 0, cr, len - 0.02, -cr, 0)
  addTri(len, 0, 0, len - 0.02, -cr, 0, len - 0.02, 0, -cr)
  addTri(len, 0, 0, len - 0.02, 0, -cr, len - 0.02, cr, 0)

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Laser Large (Paladin) - Charge laser (wider beam)
export function createLaserLargeMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.4
  const bodyW = 0.06, bodyH = 0.08

  // Boxy body
  addTri(len * 0.6, -bodyH, -bodyW, len * 0.6, -bodyH, bodyW, len * 0.6, bodyH, bodyW)
  addTri(len * 0.6, -bodyH, -bodyW, len * 0.6, bodyH, bodyW, len * 0.6, bodyH, -bodyW)
  addTri(0, -bodyH, -bodyW, 0, bodyH, -bodyW, 0, bodyH, bodyW)
  addTri(0, -bodyH, -bodyW, 0, bodyH, bodyW, 0, -bodyH, bodyW)
  addTri(0, bodyH, -bodyW, len * 0.6, bodyH, -bodyW, len * 0.6, bodyH, bodyW)
  addTri(0, bodyH, -bodyW, len * 0.6, bodyH, bodyW, 0, bodyH, bodyW)
  addTri(0, -bodyH, bodyW, len * 0.6, -bodyH, bodyW, len * 0.6, -bodyH, -bodyW)
  addTri(0, -bodyH, bodyW, len * 0.6, -bodyH, -bodyW, 0, -bodyH, -bodyW)

  // Wide emitter array (3 lenses)
  const lensR = 0.025
  for (const zOff of [-0.035, 0, 0.035]) {
    for (let i = 0; i < 6; i++) {
      const a1 = (i / 6) * Math.PI * 2
      const a2 = ((i + 1) / 6) * Math.PI * 2
      const dy1 = Math.cos(a1) * lensR, dz1 = Math.sin(a1) * lensR
      const dy2 = Math.cos(a2) * lensR, dz2 = Math.sin(a2) * lensR

      addTri(len * 0.6, dy1, zOff + dz1, len, dy1, zOff + dz1, len, dy2, zOff + dz2)
      addTri(len * 0.6, dy1, zOff + dz1, len, dy2, zOff + dz2, len * 0.6, dy2, zOff + dz2)
    }
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Lightning (Valkyrie) - Chain lightning
export function createLightningMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const len = 0.38

  // Tesla coil style body
  const baseR = 0.05, topR = 0.03
  for (let i = 0; i < 6; i++) {
    const a1 = (i / 6) * Math.PI * 2
    const a2 = ((i + 1) / 6) * Math.PI * 2
    const bdy1 = Math.cos(a1) * baseR, bdz1 = Math.sin(a1) * baseR
    const bdy2 = Math.cos(a2) * baseR, bdz2 = Math.sin(a2) * baseR
    const tdy1 = Math.cos(a1) * topR, tdz1 = Math.sin(a1) * topR
    const tdy2 = Math.cos(a2) * topR, tdz2 = Math.sin(a2) * topR

    addTri(0, bdy1, bdz1, len * 0.5, tdy1, tdz1, len * 0.5, tdy2, tdz2)
    addTri(0, bdy1, bdz1, len * 0.5, tdy2, tdz2, 0, bdy2, bdz2)
  }

  // Electrode prongs (3)
  const prongLen = 0.15, prongR = 0.015
  for (let p = 0; p < 3; p++) {
    const pa = (p / 3) * Math.PI * 2
    const px = Math.cos(pa) * 0.025
    const pz = Math.sin(pa) * 0.025

    for (let i = 0; i < 4; i++) {
      const a1 = (i / 4) * Math.PI * 2
      const a2 = ((i + 1) / 4) * Math.PI * 2
      const dy1 = Math.cos(a1) * prongR, dz1 = Math.sin(a1) * prongR
      const dy2 = Math.cos(a2) * prongR, dz2 = Math.sin(a2) * prongR

      addTri(len * 0.5 + px, dy1 + pz, dz1, len * 0.5 + prongLen, dy1, dz1, len * 0.5 + prongLen, dy2, dz2)
      addTri(len * 0.5 + px, dy1 + pz, dz1, len * 0.5 + prongLen, dy2, dz2, len * 0.5 + px, dy2 + pz, dz2)
    }
    // Ball tip
    addTri(len * 0.5 + prongLen, prongR, 0, len * 0.5 + prongLen + 0.02, 0, 0, len * 0.5 + prongLen, 0, prongR)
    addTri(len * 0.5 + prongLen, 0, prongR, len * 0.5 + prongLen + 0.02, 0, 0, len * 0.5 + prongLen, -prongR, 0)
  }

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}

// Sword (Durandal) - Energy blade
export function createSwordMesh(): MeshData {
  const vertices: number[] = []
  const addTri = createWeaponAddTri(vertices)

  const bladeLen = 0.5
  const bladeW = 0.015
  const bladeH = 0.08
  const hiltLen = 0.12

  // Blade (flat elongated diamond)
  // Top edge
  addTri(hiltLen, 0, 0, bladeLen, 0, 0, hiltLen + 0.1, bladeH * 0.5, bladeW)
  addTri(bladeLen, 0, 0, hiltLen + 0.1, bladeH * 0.5, -bladeW, hiltLen, 0, 0)
  // Bottom edge
  addTri(hiltLen, 0, 0, hiltLen + 0.1, -bladeH * 0.5, bladeW, bladeLen, 0, 0)
  addTri(hiltLen, 0, 0, bladeLen, 0, 0, hiltLen + 0.1, -bladeH * 0.5, -bladeW)
  // Sides
  addTri(hiltLen + 0.1, bladeH * 0.5, bladeW, bladeLen, 0, 0, hiltLen + 0.1, -bladeH * 0.5, bladeW)
  addTri(hiltLen + 0.1, bladeH * 0.5, -bladeW, hiltLen + 0.1, -bladeH * 0.5, -bladeW, bladeLen, 0, 0)

  // Hilt/handle
  const hiltR = 0.025
  for (let i = 0; i < 4; i++) {
    const a1 = (i / 4) * Math.PI * 2
    const a2 = ((i + 1) / 4) * Math.PI * 2
    const dy1 = Math.cos(a1) * hiltR, dz1 = Math.sin(a1) * hiltR
    const dy2 = Math.cos(a2) * hiltR, dz2 = Math.sin(a2) * hiltR

    addTri(0, dy1, dz1, hiltLen, dy1, dz1, hiltLen, dy2, dz2)
    addTri(0, dy1, dz1, hiltLen, dy2, dz2, 0, dy2, dz2)
  }

  // Cross-guard
  const guardW = 0.08, guardH = 0.02
  addTri(hiltLen - 0.01, -guardH, -guardW, hiltLen - 0.01, guardH, -guardW, hiltLen - 0.01, guardH, guardW)
  addTri(hiltLen - 0.01, -guardH, -guardW, hiltLen - 0.01, guardH, guardW, hiltLen - 0.01, -guardH, guardW)
  addTri(hiltLen + 0.01, -guardH, guardW, hiltLen + 0.01, guardH, guardW, hiltLen + 0.01, guardH, -guardW)
  addTri(hiltLen + 0.01, -guardH, guardW, hiltLen + 0.01, guardH, -guardW, hiltLen + 0.01, -guardH, -guardW)

  return { vertices: new Float32Array(vertices), vertexCount: vertices.length / 6 }
}
