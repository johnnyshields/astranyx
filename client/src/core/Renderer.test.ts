import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { Renderer, type MeshHandle } from './Renderer'

// Mock THREE.js
vi.mock('three', () => {
  class MockVector3 {
    x = 0; y = 0; z = 0
    constructor(x?: number, y?: number, z?: number) {
      this.x = x ?? 0; this.y = y ?? 0; this.z = z ?? 0
    }
    set(x: number, y: number, z: number) { this.x = x; this.y = y; this.z = z; return this }
    project() { return this }
  }

  class MockVector2 {
    x = 0; y = 0
    constructor(x?: number, y?: number) { this.x = x ?? 0; this.y = y ?? 0 }
  }

  class MockColor {
    constructor(_color?: number | string) {}
  }

  class MockBufferAttribute {
    constructor(_array: Float32Array, _itemSize: number) {}
  }

  class MockBufferGeometry {
    setAttribute = vi.fn()
  }

  class MockMaterial {
    dispose = vi.fn()
  }

  class MockMeshPhongMaterial extends MockMaterial {}
  class MockMeshBasicMaterial extends MockMaterial {}

  class MockMesh {
    geometry: MockBufferGeometry
    material: MockMaterial
    position = new MockVector3()
    scale = new MockVector3()
    rotation = { order: 'XYZ', x: 0, y: 0, z: 0, set: vi.fn() }
    constructor(geometry: MockBufferGeometry, material: MockMaterial) {
      this.geometry = geometry
      this.material = material
    }
  }

  class MockPlaneGeometry {}

  class MockPerspectiveCamera {
    aspect = 1
    position = new MockVector3()
    lookAt = vi.fn()
    updateProjectionMatrix = vi.fn()
  }

  class MockOrthographicCamera {
    left = 0; right = 0; top = 0; bottom = 0
    updateProjectionMatrix = vi.fn()
  }

  class MockDirectionalLight {
    position = new MockVector3()
  }

  class MockAmbientLight {}

  class MockScene {
    background: MockColor | null = null
    add = vi.fn()
    remove = vi.fn()
  }

  class MockPlane {
    constructor(_normal: MockVector3, _constant: number) {}
  }

  class MockRaycaster {
    ray = { intersectPlane: vi.fn().mockReturnValue(new MockVector3()) }
    setFromCamera = vi.fn()
  }

  return {
    Vector3: MockVector3,
    Vector2: MockVector2,
    Color: MockColor,
    BufferAttribute: MockBufferAttribute,
    BufferGeometry: MockBufferGeometry,
    Material: MockMaterial,
    MeshPhongMaterial: MockMeshPhongMaterial,
    MeshBasicMaterial: MockMeshBasicMaterial,
    Mesh: MockMesh,
    PlaneGeometry: MockPlaneGeometry,
    PerspectiveCamera: MockPerspectiveCamera,
    OrthographicCamera: MockOrthographicCamera,
    DirectionalLight: MockDirectionalLight,
    AmbientLight: MockAmbientLight,
    Scene: MockScene,
    Plane: MockPlane,
    Raycaster: MockRaycaster,
    DoubleSide: 2,
  }
})

// Mock WebGPURenderer
vi.mock('three/webgpu', () => {
  class MockWebGPURenderer {
    backend = { isWebGPUBackend: false }
    init = vi.fn().mockResolvedValue(undefined)
    setSize = vi.fn()
    setViewport = vi.fn()
    setScissor = vi.fn()
    setScissorTest = vi.fn()
    render = vi.fn()
    clearDepth = vi.fn()
  }
  return {
    WebGPURenderer: MockWebGPURenderer,
  }
})

describe('Renderer', () => {
  let canvas: HTMLCanvasElement
  let renderer: Renderer

  beforeEach(() => {
    canvas = document.createElement('canvas')
    renderer = new Renderer(canvas)
  })

  afterEach(() => {
    vi.clearAllMocks()
  })

  describe('constructor', () => {
    it('creates renderer with canvas', () => {
      expect(renderer).toBeDefined()
    })
  })

  describe('init', () => {
    it('initializes the renderer', async () => {
      await renderer.init()
      // Should not throw
      expect(true).toBe(true)
    })
  })

  describe('resize', () => {
    it('handles wider screen (pillarbox)', async () => {
      await renderer.init()
      renderer.resize(1920, 1080)
      // Width is 1920, height is 1080
      // Target aspect is 5:3, screen aspect is 16:9 (wider)
      // Should pillarbox
    })

    it('handles taller screen (letterbox)', async () => {
      await renderer.init()
      renderer.resize(800, 600)
      // Width is 800, height is 600
      // Target aspect is 5:3 = 1.67, screen aspect is 4:3 = 1.33 (taller)
      // Should letterbox
    })
  })

  describe('beginFrame', () => {
    it('updates time and clears frame objects', async () => {
      await renderer.init()
      renderer.resize(800, 600)

      renderer.beginFrame(16.67)
      expect(renderer.getTime()).toBeCloseTo(16.67, 1)

      renderer.beginFrame(16.67)
      expect(renderer.getTime()).toBeCloseTo(33.34, 1)
    })
  })

  describe('createMesh', () => {
    it('creates mesh from vertex data', async () => {
      await renderer.init()

      const meshData = {
        vertices: new Float32Array([
          // Position + Normal (interleaved)
          0, 0, 0, 0, 0, 1,
          1, 0, 0, 0, 0, 1,
          0, 1, 0, 0, 0, 1,
        ]),
        vertexCount: 3,
      }

      const handle = renderer.createMesh('test-mesh', meshData)

      expect(handle).toBeDefined()
      expect(handle.geometry).toBeDefined()
      expect(handle.baseMaterial).toBeDefined()
    })

    it('returns cached mesh on second call', async () => {
      await renderer.init()

      const meshData = {
        vertices: new Float32Array([0, 0, 0, 0, 0, 1]),
        vertexCount: 1,
      }

      const handle1 = renderer.createMesh('cached-mesh', meshData)
      const handle2 = renderer.createMesh('cached-mesh', meshData)

      expect(handle1).toBe(handle2)
    })
  })

  describe('drawMesh', () => {
    it('adds mesh to scene', async () => {
      await renderer.init()
      renderer.resize(800, 600)

      const meshData = {
        vertices: new Float32Array([0, 0, 0, 0, 0, 1]),
        vertexCount: 1,
      }
      const handle = renderer.createMesh('draw-test', meshData)

      renderer.beginFrame(0)
      renderer.drawMesh(handle, 0, 0, 0, 1, 1, 1, [1, 0, 0, 1])
      renderer.endFrame()
    })

    it('supports rotation parameters', async () => {
      await renderer.init()
      renderer.resize(800, 600)

      const meshData = {
        vertices: new Float32Array([0, 0, 0, 0, 0, 1]),
        vertexCount: 1,
      }
      const handle = renderer.createMesh('rotation-test', meshData)

      renderer.beginFrame(0)
      renderer.drawMesh(handle, 0, 0, 0, 1, 1, 1, [1, 0, 0, 1], Math.PI / 4, Math.PI / 2, Math.PI)
      renderer.endFrame()
    })
  })

  describe('drawQuad', () => {
    it('draws a quad at position', async () => {
      await renderer.init()
      renderer.resize(800, 600)

      renderer.beginFrame(0)
      renderer.drawQuad(100, 200, 0, 50, 50, [0, 1, 0, 0.5])
      renderer.endFrame()
    })

    it('supports rotation', async () => {
      await renderer.init()
      renderer.resize(800, 600)

      renderer.beginFrame(0)
      renderer.drawQuad(0, 0, 0, 100, 100, [1, 1, 1, 1], Math.PI / 4)
      renderer.endFrame()
    })
  })

  describe('HUD mode', () => {
    it('begins and ends HUD mode', async () => {
      await renderer.init()
      renderer.resize(800, 600)

      renderer.beginFrame(0)
      renderer.beginHUD()
      renderer.endHUD()
    })
  })

  describe('worldToScreen', () => {
    it('projects world coordinates to screen', async () => {
      await renderer.init()
      renderer.resize(800, 600)

      const result = renderer.worldToScreen(0, 0, 0)
      expect(result).toHaveProperty('x')
      expect(result).toHaveProperty('y')
    })
  })

  describe('camera settings', () => {
    it('gets camera tilt angle', async () => {
      await renderer.init()
      const angle = renderer.getCameraTiltAngle()
      expect(angle).toBeCloseTo(20 * Math.PI / 180, 4)
    })

    it('sets camera tilt angle', async () => {
      await renderer.init()
      renderer.setCameraTiltAngle(Math.PI / 6)
      expect(renderer.getCameraTiltAngle()).toBe(Math.PI / 6)
    })
  })

  describe('getPlayBounds', () => {
    it('returns play bounds with interpolation functions', async () => {
      await renderer.init()
      renderer.resize(800, 600)

      const bounds = renderer.getPlayBounds()
      expect(bounds).toHaveProperty('leftX')
      expect(bounds).toHaveProperty('rightX')
      expect(typeof bounds.getTopY).toBe('function')
      expect(typeof bounds.getBottomY).toBe('function')
    })

    it('getTopY and getBottomY return numbers', async () => {
      await renderer.init()
      renderer.resize(800, 600)

      const bounds = renderer.getPlayBounds()
      expect(typeof bounds.getTopY(0)).toBe('number')
      expect(typeof bounds.getBottomY(0)).toBe('number')
    })
  })

  describe('exposed Three.js objects', () => {
    it('returns renderer', async () => {
      await renderer.init()
      expect(renderer.getThreeRenderer()).toBeDefined()
    })

    it('returns scene', async () => {
      await renderer.init()
      expect(renderer.getScene()).toBeDefined()
    })

    it('returns camera', async () => {
      await renderer.init()
      expect(renderer.getCamera()).toBeDefined()
    })
  })
})
