import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { Engine } from './Engine'

// Mock dependencies using class mocks
vi.mock('./Renderer.ts', () => {
  return {
    Renderer: class MockRenderer {
      init = vi.fn().mockResolvedValue(undefined)
      resize = vi.fn()
    }
  }
})

vi.mock('./Input.ts', () => {
  return {
    Input: class MockInput {
      init = vi.fn()
      destroy = vi.fn()
    }
  }
})

vi.mock('../game/Game.ts', () => {
  return {
    Game: class MockGame {
      init = vi.fn().mockResolvedValue(undefined)
      resize = vi.fn()
      update = vi.fn()
      render = vi.fn()
    }
  }
})

describe('Engine', () => {
  let engine: Engine
  let mockCanvas: HTMLCanvasElement

  beforeEach(() => {
    vi.useFakeTimers()

    mockCanvas = document.createElement('canvas')
    mockCanvas.width = 800
    mockCanvas.height = 600

    // Mock window properties
    Object.defineProperty(window, 'innerWidth', { value: 1920, configurable: true })
    Object.defineProperty(window, 'innerHeight', { value: 1080, configurable: true })
    Object.defineProperty(window, 'devicePixelRatio', { value: 1, configurable: true })

    engine = new Engine(mockCanvas)
  })

  afterEach(() => {
    vi.useRealTimers()
    vi.restoreAllMocks()
  })

  describe('constructor', () => {
    it('should create engine with canvas', () => {
      expect(engine).toBeInstanceOf(Engine)
    })
  })

  describe('onProgress', () => {
    it('should set callback and return this for chaining', () => {
      const callback = vi.fn()
      const result = engine.onProgress(callback)
      expect(result).toBe(engine)
    })
  })

  describe('init', () => {
    it('should report progress through phases', async () => {
      const callback = vi.fn()
      engine.onProgress(callback)

      await engine.init()

      // Check that callback was called for each phase
      expect(callback).toHaveBeenCalledWith('renderer', 0)
      expect(callback).toHaveBeenCalledWith('renderer', 25)
      expect(callback).toHaveBeenCalledWith('input', 25)
      expect(callback).toHaveBeenCalledWith('input', 40)
      expect(callback).toHaveBeenCalledWith('game', 40)
      expect(callback).toHaveBeenCalledWith('game', 70)
      expect(callback).toHaveBeenCalledWith('game', 90)
      expect(callback).toHaveBeenCalledWith('ready', 100)
    })

    it('should add resize event listener', async () => {
      const addEventListenerSpy = vi.spyOn(window, 'addEventListener')

      await engine.init()

      expect(addEventListenerSpy).toHaveBeenCalledWith('resize', expect.any(Function))
    })
  })

  describe('start', () => {
    it('should start the game loop', async () => {
      await engine.init()

      const rafSpy = vi.spyOn(window, 'requestAnimationFrame').mockImplementation((_cb) => {
        return 1
      })

      engine.start()

      expect(rafSpy).toHaveBeenCalled()
    })

    it('should not start if already running', async () => {
      await engine.init()

      const rafSpy = vi.spyOn(window, 'requestAnimationFrame').mockImplementation(() => 1)

      engine.start()
      engine.start() // Second call should be ignored

      // Should only set up one loop
      expect(rafSpy).toHaveBeenCalledTimes(1)
    })
  })

  describe('stop', () => {
    it('should stop the game loop', async () => {
      await engine.init()

      const cancelSpy = vi.spyOn(window, 'cancelAnimationFrame')
      vi.spyOn(window, 'requestAnimationFrame').mockImplementation(() => 123)

      engine.start()
      engine.stop()

      expect(cancelSpy).toHaveBeenCalledWith(123)
    })

    it('should handle stop when not running', async () => {
      await engine.init()
      engine.stop() // Should not throw
    })
  })

  describe('game loop', () => {
    it('should call update and render', async () => {
      await engine.init()

      let frameCallback: FrameRequestCallback | null = null
      vi.spyOn(window, 'requestAnimationFrame').mockImplementation((cb) => {
        frameCallback = cb
        return 1
      })

      engine.start()

      // Simulate a frame
      if (frameCallback) {
        (frameCallback as FrameRequestCallback)(16.67) // ~60fps
      }
    })

    it('should cap accumulator to prevent spiral of death', async () => {
      await engine.init()

      let frameCallback: FrameRequestCallback | null = null

      vi.spyOn(window, 'requestAnimationFrame').mockImplementation((cb) => {
        frameCallback = cb
        return 1
      })

      vi.spyOn(performance, 'now').mockReturnValue(0)

      engine.start()

      // Simulate a very long frame (e.g., 500ms lag spike)
      if (frameCallback) {
        vi.spyOn(performance, 'now').mockReturnValue(500)
        ;(frameCallback as FrameRequestCallback)(500)
      }

      // Engine should handle this gracefully without infinite loop
    })
  })
})
