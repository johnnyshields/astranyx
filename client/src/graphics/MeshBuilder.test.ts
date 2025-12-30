import { describe, it, expect } from 'vitest'
import { MeshBuilder } from './MeshBuilder.ts'

describe('MeshBuilder', () => {
  describe('addTriangle', () => {
    it('should add triangle with 3 vertices', () => {
      const builder = new MeshBuilder()
      builder.addTriangle(0, 0, 0, 1, 0, 0, 0, 1, 0)
      expect(builder.getVertexCount()).toBe(3)
    })

    it('should calculate normals correctly', () => {
      const builder = new MeshBuilder()
      // Triangle in XY plane, should have normal pointing in +Z
      builder.addTriangle(0, 0, 0, 1, 0, 0, 0, 1, 0)
      const mesh = builder.build()

      // Check normal of first vertex (indices 3, 4, 5)
      expect(mesh.vertices[3]).toBeCloseTo(0, 5) // nx
      expect(mesh.vertices[4]).toBeCloseTo(0, 5) // ny
      expect(mesh.vertices[5]).toBeCloseTo(1, 5) // nz
    })

    it('should chain calls fluently', () => {
      const builder = new MeshBuilder()
      builder
        .addTriangle(0, 0, 0, 1, 0, 0, 0, 1, 0)
        .addTriangle(0, 0, 0, 0, 1, 0, 0, 0, 1)

      expect(builder.getVertexCount()).toBe(6)
    })
  })

  describe('addTriangleWithNormals', () => {
    it('should add triangle with explicit normals', () => {
      const builder = new MeshBuilder()
      builder.addTriangleWithNormals(
        0, 0, 0, 0, 0, 1,
        1, 0, 0, 0, 0, 1,
        0, 1, 0, 0, 0, 1
      )

      const mesh = builder.build()
      expect(mesh.vertexCount).toBe(3)
      expect(mesh.vertices[5]).toBe(1) // nz of first vertex
    })
  })

  describe('addQuad', () => {
    it('should add 6 vertices (2 triangles)', () => {
      const builder = new MeshBuilder()
      builder.addQuad(
        0, 0, 0,
        1, 0, 0,
        1, 1, 0,
        0, 1, 0
      )
      expect(builder.getVertexCount()).toBe(6)
    })
  })

  describe('addBox', () => {
    it('should add 36 vertices (6 faces * 2 triangles * 3 vertices)', () => {
      const builder = new MeshBuilder()
      builder.addBox(1, 1, 1)
      expect(builder.getVertexCount()).toBe(36)
    })

    it('should create centered box', () => {
      const builder = new MeshBuilder()
      builder.addBox(2, 2, 2)
      const mesh = builder.build()

      // Check that some vertices are at +/-1
      let foundPlusOne = false
      let foundMinusOne = false
      for (let i = 0; i < mesh.vertexCount; i++) {
        const x = mesh.vertices[i * 6]!
        if (Math.abs(x - 1) < 0.001) foundPlusOne = true
        if (Math.abs(x + 1) < 0.001) foundMinusOne = true
      }
      expect(foundPlusOne).toBe(true)
      expect(foundMinusOne).toBe(true)
    })
  })

  describe('addCylinder', () => {
    it('should add vertices for cylinder', () => {
      const builder = new MeshBuilder()
      builder.addCylinder(1, 2, 8)
      // 8 segments * (2 side triangles + 2 cap triangles) * 3 vertices = 96
      expect(builder.getVertexCount()).toBe(96)
    })

    it('should respect segment count', () => {
      const builder = new MeshBuilder()
      builder.addCylinder(1, 2, 4)
      // 4 segments * 4 triangles * 3 vertices = 48
      expect(builder.getVertexCount()).toBe(48)
    })
  })

  describe('addCone', () => {
    it('should add vertices for cone', () => {
      const builder = new MeshBuilder()
      builder.addCone(1, 2, 8)
      // 8 segments * 2 triangles (side + base) * 3 vertices = 48
      expect(builder.getVertexCount()).toBe(48)
    })
  })

  describe('addOctahedron', () => {
    it('should add 24 vertices (8 faces * 3 vertices)', () => {
      const builder = new MeshBuilder()
      builder.addOctahedron(1)
      expect(builder.getVertexCount()).toBe(24)
    })
  })

  describe('addPyramid', () => {
    it('should add 24 vertices (8 faces * 3 vertices)', () => {
      const builder = new MeshBuilder()
      builder.addPyramid(1, 1)
      expect(builder.getVertexCount()).toBe(24)
    })
  })

  describe('clear', () => {
    it('should remove all vertices', () => {
      const builder = new MeshBuilder()
      builder.addBox(1, 1, 1)
      expect(builder.getVertexCount()).toBe(36)
      builder.clear()
      expect(builder.getVertexCount()).toBe(0)
    })
  })

  describe('build', () => {
    it('should return MeshData with Float32Array', () => {
      const builder = new MeshBuilder()
      builder.addTriangle(0, 0, 0, 1, 0, 0, 0, 1, 0)
      const mesh = builder.build()

      expect(mesh.vertices).toBeInstanceOf(Float32Array)
      expect(mesh.vertexCount).toBe(3)
      expect(mesh.vertices.length).toBe(18) // 3 vertices * 6 floats
    })

    it('should return empty mesh when no vertices', () => {
      const builder = new MeshBuilder()
      const mesh = builder.build()
      expect(mesh.vertexCount).toBe(0)
      expect(mesh.vertices.length).toBe(0)
    })
  })

  describe('complex meshes', () => {
    it('should combine multiple primitives', () => {
      const builder = new MeshBuilder()
      builder
        .addBox(1, 1, 1)
        .addOctahedron(0.5)
        .addCylinder(0.2, 1, 6)

      const mesh = builder.build()
      expect(mesh.vertexCount).toBe(36 + 24 + 72) // box + octahedron + cylinder
    })
  })
})
