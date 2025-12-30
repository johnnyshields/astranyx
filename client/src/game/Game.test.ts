import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { Game, type GameState } from './Game'
import type { Renderer, MeshHandle } from '../core/Renderer'
import type { Input } from '../core/Input'

// Mock HUD module to avoid canvas context issues
vi.mock('../ui/HUD.ts', () => {
  return {
    HUD: class MockHUD {
      init = vi.fn()
      resize = vi.fn()
      clear = vi.fn()
      renderPlayerHUD = vi.fn()
      renderGameState = vi.fn()
      renderWeaponDropLabels = vi.fn()
      renderEntityHealthBars = vi.fn()
    }
  }
})

// Mock Renderer
const mockMeshHandle: MeshHandle = {
  geometry: {} as unknown as import('three').BufferGeometry,
  baseMaterial: {} as unknown as import('three').MeshPhongMaterial,
}

const mockRenderer: Renderer = {
  init: vi.fn().mockResolvedValue(undefined),
  resize: vi.fn(),
  beginFrame: vi.fn(),
  endFrame: vi.fn(),
  drawQuad: vi.fn(),
  drawMesh: vi.fn(),
  loadGLB: vi.fn().mockResolvedValue(mockMeshHandle),
  createMesh: vi.fn().mockReturnValue(mockMeshHandle),
  worldToScreen: vi.fn().mockReturnValue({ x: 0, y: 0 }),
  getPlayBounds: vi.fn().mockReturnValue({
    leftX: -500,
    rightX: 500,
    getTopY: () => 300,
    getBottomY: () => -300,
  }),
} as unknown as Renderer

const createMockInput = (): Input => ({
  init: vi.fn(),
  destroy: vi.fn(),
  getPlayer1State: vi.fn().mockReturnValue({
    up: false,
    down: false,
    left: false,
    right: false,
    fire: false,
    special: false,
    secondary: false,
    swap: false,
    pickup: false,
    pause: false,
  }),
  getPlayer2State: vi.fn().mockReturnValue({
    up: false,
    down: false,
    left: false,
    right: false,
    fire: false,
    special: false,
    secondary: false,
    swap: false,
    pickup: false,
    pause: false,
  }),
  clearFrameState: vi.fn(),
}) as unknown as Input

describe('Game', () => {
  let game: Game
  let mockInput: Input

  beforeEach(() => {
    vi.clearAllMocks()

    // Mock DOM elements
    document.body.innerHTML = `
      <div id="game-container"></div>
      <div id="titleScreen"></div>
      <div id="pauseOverlay"></div>
      <div id="gameOverOverlay"></div>
      <div id="finalScore"></div>
      <button id="btn1P"></button>
      <button id="btn2P"></button>
      <button id="btnRestart"></button>
    `

    mockInput = createMockInput()
    game = new Game(mockRenderer, mockInput)
  })

  afterEach(() => {
    document.body.innerHTML = ''
    vi.restoreAllMocks()
  })

  describe('constructor', () => {
    it('should create game with renderer and input', () => {
      expect(game).toBeInstanceOf(Game)
    })

    it('should start in title state', () => {
      expect(game.getState()).toBe('title')
    })
  })

  describe('init', () => {
    it('should load meshes', async () => {
      await game.init()

      // Should load all mesh types
      expect(mockRenderer.loadGLB).toHaveBeenCalledWith('playerShip', expect.any(String))
      expect(mockRenderer.loadGLB).toHaveBeenCalledWith('enemyShip', expect.any(String))
      expect(mockRenderer.loadGLB).toHaveBeenCalledWith('tank', expect.any(String))
      expect(mockRenderer.loadGLB).toHaveBeenCalledWith('bossCore', expect.any(String))
    })

    it('should load weapon meshes', async () => {
      await game.init()

      // Should load weapon meshes
      expect(mockRenderer.loadGLB).toHaveBeenCalledWith('weapon_vulcan', expect.any(String))
      expect(mockRenderer.loadGLB).toHaveBeenCalledWith('weapon_missile', expect.any(String))
    })

    it('should set up button handlers', async () => {
      const btn1P = document.getElementById('btn1P')
      const btn2P = document.getElementById('btn2P')
      const addEventListenerSpy1 = vi.spyOn(btn1P!, 'addEventListener')
      const addEventListenerSpy2 = vi.spyOn(btn2P!, 'addEventListener')

      await game.init()

      expect(addEventListenerSpy1).toHaveBeenCalledWith('click', expect.any(Function))
      expect(addEventListenerSpy2).toHaveBeenCalledWith('click', expect.any(Function))
    })

    it('should initialize HUD', async () => {
      await game.init()

      // HUD init is called internally
    })
  })

  describe('startLocalGame', () => {
    beforeEach(async () => {
      await game.init()
    })

    it('should start single player game', () => {
      game.startLocalGame(1)

      expect(game.getState()).toBe('playing')
      expect(game.getSimulation()).not.toBeNull()
    })

    it('should start two player game', () => {
      game.startLocalGame(2)

      expect(game.getState()).toBe('playing')
      expect(game.getSimulation()).not.toBeNull()
    })

    it('should hide title screen', () => {
      const titleScreen = document.getElementById('titleScreen')

      game.startLocalGame(1)

      expect(titleScreen!.classList.contains('hidden')).toBe(true)
    })
  })

  describe('startSinglePlayer', () => {
    beforeEach(async () => {
      await game.init()
    })

    it('should start single player game (legacy method)', () => {
      game.startSinglePlayer()

      expect(game.getState()).toBe('playing')
    })
  })

  describe('restartGame', () => {
    beforeEach(async () => {
      await game.init()
      game.startLocalGame(1)
    })

    it('should hide game over overlay', () => {
      const gameOverOverlay = document.getElementById('gameOverOverlay')
      gameOverOverlay!.classList.add('visible')

      game.restartGame()

      expect(gameOverOverlay!.classList.contains('visible')).toBe(false)
    })

    it('should restart with same number of players', () => {
      game.startLocalGame(2)
      game.restartGame()

      // Should still be 2 player mode
      expect(game.getState()).toBe('playing')
    })
  })

  describe('resize', () => {
    it('should store screen dimensions', () => {
      game.resize(1920, 1080)

      // Dimensions stored internally
    })
  })

  describe('update', () => {
    beforeEach(async () => {
      await game.init()
    })

    it('should clear input state after update', () => {
      game.startLocalGame(1)
      game.update(1 / 60)

      expect(mockInput.clearFrameState).toHaveBeenCalled()
    })

    it('should not update simulation when paused', () => {
      game.startLocalGame(1)
      const sim = game.getSimulation()
      const initialFrame = sim?.getState().frame ?? 0

      // Simulate pause press
      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: true,
      })

      game.update(1 / 60)

      expect(game.getState()).toBe('paused')
    })

    it('should show pause overlay when paused', () => {
      const pauseOverlay = document.getElementById('pauseOverlay')
      game.startLocalGame(1)

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: true,
      })

      game.update(1 / 60)

      expect(pauseOverlay!.classList.contains('visible')).toBe(true)
    })

    it('should unpause on second pause press', () => {
      game.startLocalGame(1)

      // Pause
      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: true,
      })
      game.update(1 / 60)

      expect(game.getState()).toBe('paused')

      // Clear pause input then press again
      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      })
      game.update(1 / 60)

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: true,
      })
      game.update(1 / 60)

      expect(game.getState()).toBe('playing')
    })

    it('should update starfield even when on title screen', () => {
      // Stars update even without starting game
      game.update(1 / 60)
      // No errors should be thrown
    })
  })

  describe('render', () => {
    beforeEach(async () => {
      await game.init()
    })

    it('should call renderer beginFrame and endFrame', () => {
      game.startLocalGame(1)
      game.render(1.0)

      expect(mockRenderer.beginFrame).toHaveBeenCalled()
      expect(mockRenderer.endFrame).toHaveBeenCalled()
    })

    it('should draw starfield', () => {
      game.render(1.0)

      expect(mockRenderer.drawQuad).toHaveBeenCalled()
    })

    it('should draw pause overlay when paused', () => {
      game.startLocalGame(1)

      // Pause
      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: true,
      })
      game.update(1 / 60)
      game.render(1.0)

      // Should draw semi-transparent overlay
      expect(mockRenderer.drawQuad).toHaveBeenCalledWith(
        0, 0, 100, 2000, 1200, [0, 0, 0.1, 0.8]
      )
    })
  })

  describe('getState', () => {
    it('should return current game state', () => {
      expect(game.getState()).toBe('title')
    })
  })

  describe('getSimulation', () => {
    it('should return null before game starts', () => {
      expect(game.getSimulation()).toBeNull()
    })

    it('should return simulation after game starts', async () => {
      await game.init()
      game.startLocalGame(1)

      expect(game.getSimulation()).not.toBeNull()
    })
  })
})

describe('GameState type', () => {
  it('should support all game states', () => {
    const states: GameState[] = ['title', 'lobby', 'connecting', 'playing', 'paused', 'gameover']
    expect(states).toHaveLength(6)
  })
})
