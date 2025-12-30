import { describe, it, expect } from 'vitest'
import {
  createBoxMesh,
  createPlayerShipMesh,
  createEnemyShipMesh,
  createTankMesh,
  createBossCoreMesh,
  createDroneMesh,
  createOrbMesh,
  createPowerupMesh,
  createMineMesh,
  createVulcanMesh,
  createShotgunMesh,
  createSpreadSmallMesh,
  createSpreadLargeMesh,
  createRailgunMesh,
  createMissileMesh,
  createCannonMesh,
  createLimpetMesh,
  createGrenadeMesh,
  createFlameMesh,
  createAcidMesh,
  createSonicMesh,
  createLaserSmallMesh,
  createLaserLargeMesh,
  createLightningMesh,
  createSwordMesh,
  type MeshData,
} from './MeshGenerator'

function validateMeshData(mesh: MeshData, name: string) {
  // Vertices should be Float32Array
  expect(mesh.vertices).toBeInstanceOf(Float32Array)

  // Vertex count should match array size (6 floats per vertex: x, y, z, nx, ny, nz)
  expect(mesh.vertices.length).toBe(mesh.vertexCount * 6)

  // Should have at least one triangle (3 vertices)
  expect(mesh.vertexCount).toBeGreaterThanOrEqual(3)

  // Vertex count should be divisible by 3 (triangles)
  expect(mesh.vertexCount % 3).toBe(0)

  // All values should be finite
  for (let i = 0; i < mesh.vertices.length; i++) {
    expect(Number.isFinite(mesh.vertices[i]!)).toBe(true)
  }

  // Normals should be roughly normalized (length close to 1)
  for (let i = 0; i < mesh.vertexCount; i++) {
    const nx = mesh.vertices[i * 6 + 3]!
    const ny = mesh.vertices[i * 6 + 4]!
    const nz = mesh.vertices[i * 6 + 5]!
    const len = Math.sqrt(nx * nx + ny * ny + nz * nz)
    // Allow for some degenerate triangles with zero normals
    if (len > 0.01) {
      expect(len).toBeCloseTo(1, 1) // Within 0.1 of 1.0
    }
  }
}

describe('MeshGenerator', () => {
  describe('createBoxMesh', () => {
    it('should create a valid box mesh', () => {
      const mesh = createBoxMesh(1, 2, 3)
      validateMeshData(mesh, 'box')
    })

    it('should create 36 vertices (6 faces * 2 triangles * 3 vertices)', () => {
      const mesh = createBoxMesh(1, 1, 1)
      expect(mesh.vertexCount).toBe(36)
    })

    it('should scale with dimensions', () => {
      const mesh = createBoxMesh(2, 4, 6)
      validateMeshData(mesh, 'scaled box')

      // Check that vertices are within expected bounds
      let maxX = -Infinity, maxY = -Infinity, maxZ = -Infinity
      let minX = Infinity, minY = Infinity, minZ = Infinity

      for (let i = 0; i < mesh.vertexCount; i++) {
        const x = mesh.vertices[i * 6]!
        const y = mesh.vertices[i * 6 + 1]!
        const z = mesh.vertices[i * 6 + 2]!
        maxX = Math.max(maxX, x)
        maxY = Math.max(maxY, y)
        maxZ = Math.max(maxZ, z)
        minX = Math.min(minX, x)
        minY = Math.min(minY, y)
        minZ = Math.min(minZ, z)
      }

      expect(maxX - minX).toBeCloseTo(2, 5)
      expect(maxY - minY).toBeCloseTo(4, 5)
      expect(maxZ - minZ).toBeCloseTo(6, 5)
    })
  })

  describe('Entity Meshes', () => {
    it('should create valid player ship mesh', () => {
      const mesh = createPlayerShipMesh()
      validateMeshData(mesh, 'player ship')
      expect(mesh.vertexCount).toBeGreaterThan(30) // Complex mesh
    })

    it('should create valid enemy ship mesh', () => {
      const mesh = createEnemyShipMesh()
      validateMeshData(mesh, 'enemy ship')
    })

    it('should create valid tank mesh', () => {
      const mesh = createTankMesh()
      validateMeshData(mesh, 'tank')
    })

    it('should create valid boss core mesh', () => {
      const mesh = createBossCoreMesh()
      validateMeshData(mesh, 'boss core')
    })

    it('should create valid drone mesh', () => {
      const mesh = createDroneMesh()
      validateMeshData(mesh, 'drone')
    })

    it('should create valid orb mesh', () => {
      const mesh = createOrbMesh()
      validateMeshData(mesh, 'orb')
    })

    it('should create valid powerup mesh', () => {
      const mesh = createPowerupMesh()
      validateMeshData(mesh, 'powerup')
    })

    it('should create valid mine mesh', () => {
      const mesh = createMineMesh()
      validateMeshData(mesh, 'mine')
    })
  })

  describe('Weapon Meshes - Bullet Type', () => {
    it('should create valid vulcan mesh', () => {
      const mesh = createVulcanMesh()
      validateMeshData(mesh, 'vulcan')
    })

    it('should create valid shotgun mesh', () => {
      const mesh = createShotgunMesh()
      validateMeshData(mesh, 'shotgun')
    })

    it('should create valid spread small mesh', () => {
      const mesh = createSpreadSmallMesh()
      validateMeshData(mesh, 'spread small')
    })

    it('should create valid spread large mesh', () => {
      const mesh = createSpreadLargeMesh()
      validateMeshData(mesh, 'spread large')
    })

    it('should create valid railgun mesh', () => {
      const mesh = createRailgunMesh()
      validateMeshData(mesh, 'railgun')
    })
  })

  describe('Weapon Meshes - Bomb Type', () => {
    it('should create valid missile mesh', () => {
      const mesh = createMissileMesh()
      validateMeshData(mesh, 'missile')
    })

    it('should create valid cannon mesh', () => {
      const mesh = createCannonMesh()
      validateMeshData(mesh, 'cannon')
    })

    it('should create valid limpet mesh', () => {
      const mesh = createLimpetMesh()
      validateMeshData(mesh, 'limpet')
    })

    it('should create valid grenade mesh', () => {
      const mesh = createGrenadeMesh()
      validateMeshData(mesh, 'grenade')
    })
  })

  describe('Weapon Meshes - Oil Type', () => {
    it('should create valid flame mesh', () => {
      const mesh = createFlameMesh()
      validateMeshData(mesh, 'flame')
    })

    it('should create valid acid mesh', () => {
      const mesh = createAcidMesh()
      validateMeshData(mesh, 'acid')
    })
  })

  describe('Weapon Meshes - Energy Type', () => {
    it('should create valid sonic mesh', () => {
      const mesh = createSonicMesh()
      validateMeshData(mesh, 'sonic')
    })

    it('should create valid laser small mesh', () => {
      const mesh = createLaserSmallMesh()
      validateMeshData(mesh, 'laser small')
    })

    it('should create valid laser large mesh', () => {
      const mesh = createLaserLargeMesh()
      validateMeshData(mesh, 'laser large')
    })

    it('should create valid lightning mesh', () => {
      const mesh = createLightningMesh()
      validateMeshData(mesh, 'lightning')
    })

    it('should create valid sword mesh', () => {
      const mesh = createSwordMesh()
      validateMeshData(mesh, 'sword')
    })
  })

  describe('Mesh Properties', () => {
    it('player ship should be oriented forward (+X)', () => {
      const mesh = createPlayerShipMesh()

      // Find the nose (max X coordinate)
      let maxX = -Infinity
      for (let i = 0; i < mesh.vertexCount; i++) {
        maxX = Math.max(maxX, mesh.vertices[i * 6]!)
      }

      // Nose should be in positive X direction
      expect(maxX).toBeGreaterThan(0.3)
    })

    it('enemy ship should face left (-X)', () => {
      const mesh = createEnemyShipMesh()

      // Find the nose (min X coordinate, as enemy faces left)
      let minX = Infinity
      for (let i = 0; i < mesh.vertexCount; i++) {
        minX = Math.min(minX, mesh.vertices[i * 6]!)
      }

      // Nose should be in negative X direction
      expect(minX).toBeLessThan(-0.3)
    })

    it('all meshes should be reasonably sized (< 1 unit)', () => {
      const meshFunctions = [
        createPlayerShipMesh,
        createEnemyShipMesh,
        createTankMesh,
        createBossCoreMesh,
        createDroneMesh,
        createOrbMesh,
        createPowerupMesh,
      ]

      for (const fn of meshFunctions) {
        const mesh = fn()
        let maxDist = 0

        for (let i = 0; i < mesh.vertexCount; i++) {
          const x = mesh.vertices[i * 6]!
          const y = mesh.vertices[i * 6 + 1]!
          const z = mesh.vertices[i * 6 + 2]!
          const dist = Math.sqrt(x * x + y * y + z * z)
          maxDist = Math.max(maxDist, dist)
        }

        // All meshes should fit within 1 unit radius
        expect(maxDist).toBeLessThan(1)
      }
    })

    it('weapon meshes should be smaller than entity meshes', () => {
      const weaponMesh = createVulcanMesh()
      const entityMesh = createPlayerShipMesh()

      let weaponMaxDist = 0
      let entityMaxDist = 0

      for (let i = 0; i < weaponMesh.vertexCount; i++) {
        const x = weaponMesh.vertices[i * 6]!
        const y = weaponMesh.vertices[i * 6 + 1]!
        const z = weaponMesh.vertices[i * 6 + 2]!
        weaponMaxDist = Math.max(weaponMaxDist, Math.sqrt(x * x + y * y + z * z))
      }

      for (let i = 0; i < entityMesh.vertexCount; i++) {
        const x = entityMesh.vertices[i * 6]!
        const y = entityMesh.vertices[i * 6 + 1]!
        const z = entityMesh.vertices[i * 6 + 2]!
        entityMaxDist = Math.max(entityMaxDist, Math.sqrt(x * x + y * y + z * z))
      }

      expect(weaponMaxDist).toBeLessThan(entityMaxDist)
    })
  })

  describe('Consistency', () => {
    it('should produce deterministic meshes', () => {
      const mesh1 = createPlayerShipMesh()
      const mesh2 = createPlayerShipMesh()

      expect(mesh1.vertexCount).toBe(mesh2.vertexCount)

      for (let i = 0; i < mesh1.vertices.length; i++) {
        expect(mesh1.vertices[i]).toBe(mesh2.vertices[i])
      }
    })
  })
})
