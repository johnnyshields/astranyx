/**
 * Export procedural meshes to GLB files for use in Blender or WebGL
 *
 * Run with: bun run scripts/export-meshes.ts
 */

import {
  createPlayerShipMesh,
  createEnemyShipMesh,
  createTankMesh,
  createBossCoreMesh,
  createDroneMesh,
  createOrbMesh,
  createPowerupMesh,
  createMineMesh,
  type MeshData,
} from '../src/graphics/MeshGenerator.ts'

// glTF 2.0 constants
const GLTF_COMPONENT_TYPE_FLOAT = 5126
const GLTF_ARRAY_BUFFER = 34962
const GLTF_TRIANGLES = 4

interface GltfBuffer {
  uri: string
  byteLength: number
}

interface GltfBufferView {
  buffer: number
  byteOffset: number
  byteLength: number
  target?: number
}

interface GltfAccessor {
  bufferView: number
  byteOffset: number
  componentType: number
  count: number
  type: string
  min?: number[]
  max?: number[]
}

interface GltfMesh {
  name: string
  primitives: Array<{
    attributes: { POSITION: number; NORMAL: number }
    mode: number
  }>
}

interface GltfNode {
  mesh: number
  name: string
}

interface GltfScene {
  nodes: number[]
}

interface Gltf {
  asset: { version: string; generator: string }
  scene: number
  scenes: GltfScene[]
  nodes: GltfNode[]
  meshes: GltfMesh[]
  accessors: GltfAccessor[]
  bufferViews: GltfBufferView[]
  buffers: GltfBuffer[]
}

function meshDataToGlb(meshData: MeshData, name: string): Uint8Array {
  // Extract positions and normals from interleaved vertex data
  const vertexCount = meshData.vertexCount
  const positions = new Float32Array(vertexCount * 3)
  const normals = new Float32Array(vertexCount * 3)

  for (let i = 0; i < vertexCount; i++) {
    const srcIdx = i * 6
    const dstIdx = i * 3
    // Position (x, y, z)
    positions[dstIdx] = meshData.vertices[srcIdx]!
    positions[dstIdx + 1] = meshData.vertices[srcIdx + 1]!
    positions[dstIdx + 2] = meshData.vertices[srcIdx + 2]!
    // Normal (nx, ny, nz)
    normals[dstIdx] = meshData.vertices[srcIdx + 3]!
    normals[dstIdx + 1] = meshData.vertices[srcIdx + 4]!
    normals[dstIdx + 2] = meshData.vertices[srcIdx + 5]!
  }

  // Calculate bounding box for positions
  let minX = Infinity, minY = Infinity, minZ = Infinity
  let maxX = -Infinity, maxY = -Infinity, maxZ = -Infinity
  for (let i = 0; i < vertexCount; i++) {
    const x = positions[i * 3]!
    const y = positions[i * 3 + 1]!
    const z = positions[i * 3 + 2]!
    minX = Math.min(minX, x)
    minY = Math.min(minY, y)
    minZ = Math.min(minZ, z)
    maxX = Math.max(maxX, x)
    maxY = Math.max(maxY, y)
    maxZ = Math.max(maxZ, z)
  }

  // Create binary buffer (positions + normals)
  const positionsByteLength = positions.byteLength
  const normalsByteLength = normals.byteLength
  const totalByteLength = positionsByteLength + normalsByteLength

  // Pad to 4-byte alignment
  const paddedByteLength = Math.ceil(totalByteLength / 4) * 4
  const binaryBuffer = new ArrayBuffer(paddedByteLength)
  const binaryView = new Uint8Array(binaryBuffer)

  // Copy positions
  binaryView.set(new Uint8Array(positions.buffer), 0)
  // Copy normals
  binaryView.set(new Uint8Array(normals.buffer), positionsByteLength)

  // Build glTF JSON
  const gltf: Gltf = {
    asset: {
      version: '2.0',
      generator: 'Astranyx Mesh Exporter',
    },
    scene: 0,
    scenes: [{ nodes: [0] }],
    nodes: [{ mesh: 0, name }],
    meshes: [
      {
        name,
        primitives: [
          {
            attributes: {
              POSITION: 0,
              NORMAL: 1,
            },
            mode: GLTF_TRIANGLES,
          },
        ],
      },
    ],
    accessors: [
      {
        bufferView: 0,
        byteOffset: 0,
        componentType: GLTF_COMPONENT_TYPE_FLOAT,
        count: vertexCount,
        type: 'VEC3',
        min: [minX, minY, minZ],
        max: [maxX, maxY, maxZ],
      },
      {
        bufferView: 1,
        byteOffset: 0,
        componentType: GLTF_COMPONENT_TYPE_FLOAT,
        count: vertexCount,
        type: 'VEC3',
      },
    ],
    bufferViews: [
      {
        buffer: 0,
        byteOffset: 0,
        byteLength: positionsByteLength,
        target: GLTF_ARRAY_BUFFER,
      },
      {
        buffer: 0,
        byteOffset: positionsByteLength,
        byteLength: normalsByteLength,
        target: GLTF_ARRAY_BUFFER,
      },
    ],
    buffers: [
      {
        uri: '', // Will be embedded in GLB
        byteLength: paddedByteLength,
      },
    ],
  }

  // Encode JSON
  const jsonString = JSON.stringify(gltf)
  const jsonBuffer = new TextEncoder().encode(jsonString)
  // Pad JSON to 4-byte alignment
  const jsonPaddedLength = Math.ceil(jsonBuffer.length / 4) * 4
  const jsonPadded = new Uint8Array(jsonPaddedLength)
  jsonPadded.set(jsonBuffer)
  // Pad with spaces (0x20) as per glTF spec
  for (let i = jsonBuffer.length; i < jsonPaddedLength; i++) {
    jsonPadded[i] = 0x20
  }

  // Build GLB file
  // Header: magic (4) + version (4) + length (4) = 12 bytes
  // JSON chunk: length (4) + type (4) + data
  // BIN chunk: length (4) + type (4) + data
  const glbLength = 12 + 8 + jsonPaddedLength + 8 + paddedByteLength
  const glb = new ArrayBuffer(glbLength)
  const glbView = new DataView(glb)
  const glbBytes = new Uint8Array(glb)

  let offset = 0

  // GLB Header
  glbView.setUint32(offset, 0x46546C67, true) // 'glTF' magic
  offset += 4
  glbView.setUint32(offset, 2, true) // version 2
  offset += 4
  glbView.setUint32(offset, glbLength, true) // total length
  offset += 4

  // JSON chunk
  glbView.setUint32(offset, jsonPaddedLength, true) // chunk length
  offset += 4
  glbView.setUint32(offset, 0x4E4F534A, true) // 'JSON' type
  offset += 4
  glbBytes.set(jsonPadded, offset)
  offset += jsonPaddedLength

  // BIN chunk
  glbView.setUint32(offset, paddedByteLength, true) // chunk length
  offset += 4
  glbView.setUint32(offset, 0x004E4942, true) // 'BIN\0' type
  offset += 4
  glbBytes.set(binaryView, offset)

  return new Uint8Array(glb)
}

async function exportMeshes() {
  const outputDir = './public/assets/meshes'

  const meshes: Array<{ name: string; data: MeshData }> = [
    { name: 'player-ship', data: createPlayerShipMesh() },
    { name: 'enemy-ship', data: createEnemyShipMesh() },
    { name: 'tank', data: createTankMesh() },
    { name: 'boss-core', data: createBossCoreMesh() },
    { name: 'drone', data: createDroneMesh() },
    { name: 'orb', data: createOrbMesh() },
    { name: 'powerup', data: createPowerupMesh() },
    { name: 'mine', data: createMineMesh() },
  ]

  for (const mesh of meshes) {
    const glb = meshDataToGlb(mesh.data, mesh.name)
    const path = `${outputDir}/${mesh.name}.glb`
    await Bun.write(path, glb)
    console.log(`Exported: ${path} (${glb.byteLength} bytes, ${mesh.data.vertexCount} vertices)`)
  }

  console.log('\nAll meshes exported successfully!')
}

exportMeshes().catch(console.error)
