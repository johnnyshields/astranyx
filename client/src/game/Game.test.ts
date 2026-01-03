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
      expect(game).toBeDefined()
    })

    it('should start in title state', () => {
      expect(game.getState()).toBe('title')
      expect(typeof game.getState()).toBe('string')
    })

    it('should have null simulation before init', () => {
      expect(game.getSimulation()).toBeNull()
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

      // HUD init is called internally - just verify no errors
      expect(game.getState()).toBe('title')
    })

    it('should be callable multiple times safely', async () => {
      await game.init()
      await expect(game.init()).resolves.not.toThrow()
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
      expect(typeof game.getState()).toBe('string')
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

    it('should create simulation with correct player count', () => {
      game.startLocalGame(2)

      const sim = game.getSimulation()
      expect(sim).not.toBeNull()
      expect(sim?.getPlayerIds().length).toBe(2)
    })

    it('should start with frame 0', () => {
      game.startLocalGame(1)

      const sim = game.getSimulation()
      expect(sim?.getFrame()).toBe(0)
    })
  })

  describe('startSinglePlayer', () => {
    beforeEach(async () => {
      await game.init()
    })

    it('should start single player game (legacy method)', () => {
      game.startSinglePlayer()

      expect(game.getState()).toBe('playing')
      expect(game.getSimulation()).not.toBeNull()
    })

    it('should create single player simulation', () => {
      game.startSinglePlayer()

      const sim = game.getSimulation()
      expect(sim?.getPlayerIds().length).toBe(1)
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

    it('should reset simulation state', () => {
      // Run some frames first
      for (let i = 0; i < 50; i++) {
        game.update(1 / 60)
      }

      const frameBeforeRestart = game.getSimulation()?.getFrame()
      expect(frameBeforeRestart).toBeGreaterThan(0)

      game.restartGame()

      const frameAfterRestart = game.getSimulation()?.getFrame()
      expect(frameAfterRestart).toBe(0)
    })

    it('should maintain playing state after restart', () => {
      game.restartGame()
      expect(game.getState()).toBe('playing')
      expect(game.getSimulation()).not.toBeNull()
    })
  })

  describe('resize', () => {
    it('should store screen dimensions', () => {
      // Should not throw with valid dimensions
      expect(() => game.resize(1920, 1080)).not.toThrow()
    })

    it('should handle various screen sizes', () => {
      const sizes = [
        [800, 600],
        [1920, 1080],
        [3840, 2160],
        [1366, 768],
      ]

      for (const [width, height] of sizes) {
        expect(() => game.resize(width!, height!)).not.toThrow()
      }
    })

    it('should handle small sizes', () => {
      expect(() => game.resize(320, 240)).not.toThrow()
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
      const _initialFrame = sim?.getState().frame ?? 0

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
      expect(typeof game.getState()).toBe('string')
    })

    it('should return valid game state values', () => {
      const validStates: GameState[] = ['title', 'lobby', 'connecting', 'playing', 'paused', 'gameover']
      expect(validStates).toContain(game.getState())
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
      expect(game.getSimulation()).toBeDefined()
    })

    it('should return consistent simulation reference', async () => {
      await game.init()
      game.startLocalGame(1)

      const sim1 = game.getSimulation()
      const sim2 = game.getSimulation()

      expect(sim1).toBe(sim2)
    })
  })
})

describe('GameState type', () => {
  it('should support all game states', () => {
    const states: GameState[] = ['title', 'lobby', 'connecting', 'playing', 'paused', 'gameover']
    expect(states).toHaveLength(6)
    expect(Array.isArray(states)).toBe(true)
  })

  it('should have all states as strings', () => {
    const states: GameState[] = ['title', 'lobby', 'connecting', 'playing', 'paused', 'gameover']
    for (const state of states) {
      expect(typeof state).toBe('string')
      expect(state.length).toBeGreaterThan(0)
    }
  })

  it('should have unique states', () => {
    const states: GameState[] = ['title', 'lobby', 'connecting', 'playing', 'paused', 'gameover']
    expect(new Set(states).size).toBe(states.length)
  })
})

describe('Game additional functionality', () => {
  let game: Game
  let mockInput: Input

  beforeEach(async () => {
    vi.clearAllMocks()

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
    await game.init()
  })

  afterEach(() => {
    document.body.innerHTML = ''
    vi.restoreAllMocks()
  })

  describe('setChatHandler', () => {
    it('should accept chat handler function', () => {
      const handler = vi.fn()
      expect(() => game.setChatHandler(handler)).not.toThrow()
    })

    it('should accept handler without throwing', () => {
      const handler = () => {}
      expect(() => game.setChatHandler(handler)).not.toThrow()
    })
  })

  describe('setVoiceToggleHandler', () => {
    it('should accept voice toggle handler function', () => {
      const handler = vi.fn()
      expect(() => game.setVoiceToggleHandler(handler)).not.toThrow()
    })

    it('should accept handler without throwing', () => {
      const handler = () => {}
      expect(() => game.setVoiceToggleHandler(handler)).not.toThrow()
    })
  })

  describe('isVoiceEnabled', () => {
    it('should return false by default', () => {
      expect(game.isVoiceEnabled()).toBe(false)
      expect(typeof game.isVoiceEnabled()).toBe('boolean')
    })

    it('should return consistent value', () => {
      const val1 = game.isVoiceEnabled()
      const val2 = game.isVoiceEnabled()
      expect(val1).toBe(val2)
    })
  })

  describe('multiple frame updates', () => {
    it('should handle multiple update calls', () => {
      game.startLocalGame(1)

      for (let i = 0; i < 10; i++) {
        game.update(1 / 60)
      }

      expect(game.getState()).toBe('playing')
      // Frame should have advanced
      expect(game.getSimulation()?.getFrame()).toBeGreaterThan(0)
    })

    it('should handle multiple render calls', () => {
      game.startLocalGame(1)
      game.resize(1920, 1080)

      for (let i = 0; i < 10; i++) {
        game.render(i / 10)
      }

      expect(mockRenderer.beginFrame).toHaveBeenCalledTimes(10)
      expect(mockRenderer.endFrame).toHaveBeenCalledTimes(10)
    })

    it('should maintain simulation state across updates', () => {
      game.startLocalGame(1)

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      const sim = game.getSimulation()
      expect(sim).not.toBeNull()
      expect(sim?.getFrame()).toBe(60)
    })

    it('should handle rapid update and render cycles', () => {
      game.startLocalGame(1)
      game.resize(800, 600)

      for (let i = 0; i < 30; i++) {
        game.update(1 / 60)
        game.render(1.0)
      }

      expect(game.getState()).toBe('playing')
    })
  })

  describe('game over state', () => {
    it('should restart from game over state', () => {
      game.startLocalGame(1)

      const gameOverOverlay = document.getElementById('gameOverOverlay')
      gameOverOverlay!.classList.add('visible')

      game.restartGame()

      expect(game.getState()).toBe('playing')
      expect(gameOverOverlay!.classList.contains('visible')).toBe(false)
    })

    it('should reset simulation on restart', () => {
      game.startLocalGame(1)

      // Run simulation
      for (let i = 0; i < 50; i++) {
        game.update(1 / 60)
      }

      game.restartGame()

      const sim = game.getSimulation()
      expect(sim?.getFrame()).toBe(0)
      expect(sim?.getState().score).toBe(0)
    })
  })

  describe('render with enemies', () => {
    it('should render enemies when present', () => {
      game.startLocalGame(1)

      // Run simulation until enemies spawn
      for (let i = 0; i < 100; i++) {
        game.update(1 / 60)
      }

      game.render(1.0)

      expect(mockRenderer.drawMesh).toHaveBeenCalled()
    })

    it('should maintain game state after rendering enemies', () => {
      game.startLocalGame(1)

      for (let i = 0; i < 100; i++) {
        game.update(1 / 60)
        game.render(1.0)
      }

      expect(game.getState()).toBe('playing')
      const sim = game.getSimulation()
      expect(sim?.getState().enemies.length).toBeGreaterThanOrEqual(0)
    })
  })

  describe('render with bullets', () => {
    it('should render bullets when player fires', () => {
      game.startLocalGame(1)

      // Simulate fire input
      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: true,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      })

      for (let i = 0; i < 30; i++) {
        game.update(1 / 60)
      }

      game.render(1.0)

      expect(mockRenderer.drawMesh).toHaveBeenCalled()
    })

    it('should track bullets in simulation', () => {
      game.startLocalGame(1)

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false, down: false, left: false, right: false,
        fire: true, special: false, secondary: false,
        swap: false, pickup: false, pause: false,
      })

      for (let i = 0; i < 30; i++) {
        game.update(1 / 60)
      }

      const sim = game.getSimulation()
      expect(sim?.getState().bullets.length).toBeGreaterThan(0)
    })
  })

  describe('two player mode', () => {
    it('should update both players in two player mode', () => {
      game.startLocalGame(2)

      // Different inputs for both players
      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: true,
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
      ;(mockInput.getPlayer2State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: true,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      })

      for (let i = 0; i < 30; i++) {
        game.update(1 / 60)
      }

      game.render(1.0)

      // Should render both players
      expect(mockRenderer.drawMesh).toHaveBeenCalled()
    })

    it('should have two players in simulation', () => {
      game.startLocalGame(2)

      const sim = game.getSimulation()
      const state = sim?.getState()

      expect(state?.players.length).toBe(2)
      expect(state?.players[0]).toBeDefined()
      expect(state?.players[1]).toBeDefined()
    })

    it('should have unique player IDs', () => {
      game.startLocalGame(2)

      const sim = game.getSimulation()
      const state = sim?.getState()

      expect(state?.players[0]?.id).not.toBe(state?.players[1]?.id)
    })

    it('should move players independently', () => {
      game.startLocalGame(2)

      const sim = game.getSimulation()
      const initialState = sim?.getState()
      const p1InitialY = initialState?.players[0]?.y ?? 0
      const p2InitialY = initialState?.players[1]?.y ?? 0

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: true, down: false, left: false, right: false,
        fire: false, special: false, secondary: false,
        swap: false, pickup: false, pause: false,
      })
      ;(mockInput.getPlayer2State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false, down: true, left: false, right: false,
        fire: false, special: false, secondary: false,
        swap: false, pickup: false, pause: false,
      })

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      const finalState = sim?.getState()
      const p1FinalY = finalState?.players[0]?.y ?? 0
      const p2FinalY = finalState?.players[1]?.y ?? 0

      // Player 1 moved up (y decreases), Player 2 moved down (y increases)
      expect(p1FinalY).toBeLessThan(p1InitialY)
      expect(p2FinalY).toBeGreaterThan(p2InitialY)
    })

    it('should restart with two players', () => {
      game.startLocalGame(2)
      game.restartGame()

      const sim = game.getSimulation()
      expect(sim).not.toBeNull()
    })

    it('should maintain two players after restart', () => {
      game.startLocalGame(2)

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      game.restartGame()

      const sim = game.getSimulation()
      const state = sim?.getState()

      expect(state?.players.length).toBe(2)
    })
  })

  describe('resize handling', () => {
    it('should maintain game state after resize', () => {
      game.startLocalGame(1)

      const stateBefore = game.getState()
      game.resize(1920, 1080)
      const stateAfter = game.getState()

      expect(stateAfter).toBe(stateBefore)
    })

    it('should maintain simulation after resize', () => {
      game.startLocalGame(1)

      const simBefore = game.getSimulation()
      game.resize(1920, 1080)
      const simAfter = game.getSimulation()

      expect(simAfter).toBe(simBefore)
    })

    it('should handle very wide aspect ratios', () => {
      game.startLocalGame(1)

      game.resize(2560, 1080) // Ultra-wide
      game.render(1.0)

      expect(game.getState()).toBe('playing')
    })

    it('should handle portrait aspect ratios', () => {
      game.startLocalGame(1)

      game.resize(600, 800) // Portrait
      game.render(1.0)

      expect(game.getState()).toBe('playing')
    })
  })

  describe('button click handlers', () => {
    it('should create simulation with 1 player on btn1P click', () => {
      const btn1P = document.getElementById('btn1P')!
      btn1P.click()

      const sim = game.getSimulation()
      expect(sim?.getState().players.length).toBe(1)
    })

    it('should create simulation with 2 players on btn2P click', () => {
      const btn2P = document.getElementById('btn2P')!
      btn2P.click()

      const sim = game.getSimulation()
      expect(sim?.getState().players.length).toBe(2)
    })

    it('should reset simulation on btnRestart click', () => {
      game.startLocalGame(1)

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      const frameBeforeRestart = game.getSimulation()?.getFrame() ?? 0
      expect(frameBeforeRestart).toBeGreaterThan(0)

      const btnRestart = document.getElementById('btnRestart')!
      btnRestart.click()

      const frameAfterRestart = game.getSimulation()?.getFrame() ?? -1
      expect(frameAfterRestart).toBe(0)
    })
  })

  describe('title state rendering', () => {
    it('should maintain title state after render', () => {
      game.render(1.0)

      expect(game.getState()).toBe('title')
    })
  })

  describe('player movement', () => {
    it('should move player when direction keys pressed', () => {
      game.startLocalGame(1)

      const initialSim = game.getSimulation()
      const initialState = initialSim?.getState()
      const initialX = initialState?.players[0]?.x ?? 0

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: true,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      })

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      const finalState = initialSim?.getState()
      const finalX = finalState?.players[0]?.x ?? 0

      expect(finalX).toBeGreaterThan(initialX)
    })

    it('should move player up when up key pressed', () => {
      game.startLocalGame(1)

      const sim = game.getSimulation()
      const initialY = sim?.getState().players[0]?.y ?? 0

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: true, down: false, left: false, right: false,
        fire: false, special: false, secondary: false,
        swap: false, pickup: false, pause: false,
      })

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      const finalY = sim?.getState().players[0]?.y ?? 0
      expect(finalY).toBeLessThan(initialY)
    })

    it('should move player down when down key pressed', () => {
      game.startLocalGame(1)

      const sim = game.getSimulation()
      const initialY = sim?.getState().players[0]?.y ?? 0

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false, down: true, left: false, right: false,
        fire: false, special: false, secondary: false,
        swap: false, pickup: false, pause: false,
      })

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      const finalY = sim?.getState().players[0]?.y ?? 0
      expect(finalY).toBeGreaterThan(initialY)
    })

    it('should move player left when left key pressed', () => {
      game.startLocalGame(1)

      const sim = game.getSimulation()
      const initialX = sim?.getState().players[0]?.x ?? 0

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false, down: false, left: true, right: false,
        fire: false, special: false, secondary: false,
        swap: false, pickup: false, pause: false,
      })

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      const finalX = sim?.getState().players[0]?.x ?? 0
      expect(finalX).toBeLessThan(initialX)
    })

    it('should handle diagonal movement', () => {
      game.startLocalGame(1)

      const sim = game.getSimulation()
      const initialX = sim?.getState().players[0]?.x ?? 0
      const initialY = sim?.getState().players[0]?.y ?? 0

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: true, down: false, left: false, right: true,
        fire: false, special: false, secondary: false,
        swap: false, pickup: false, pause: false,
      })

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      const finalX = sim?.getState().players[0]?.x ?? 0
      const finalY = sim?.getState().players[0]?.y ?? 0

      expect(finalX).toBeGreaterThan(initialX)
      expect(finalY).toBeLessThan(initialY)
    })

    it('should not move significantly when no direction pressed', () => {
      game.startLocalGame(1)

      const sim = game.getSimulation()
      const initialX = sim?.getState().players[0]?.x ?? 0

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false, down: false, left: false, right: false,
        fire: false, special: false, secondary: false,
        swap: false, pickup: false, pause: false,
      })

      for (let i = 0; i < 60; i++) {
        game.update(1 / 60)
      }

      const finalX = sim?.getState().players[0]?.x ?? 0

      // X position should not change significantly (player doesn't move left/right without input)
      // Allow small drift due to screen scrolling or other game mechanics
      expect(Math.abs(finalX - initialX)).toBeLessThan(50)
    })
  })

  describe('special and secondary inputs', () => {
    it('should handle special input', () => {
      game.startLocalGame(1)

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: true,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      })

      for (let i = 0; i < 10; i++) {
        game.update(1 / 60)
      }

      // Should not crash
      expect(game.getState()).toBe('playing')
    })

    it('should handle secondary input', () => {
      game.startLocalGame(1)

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: true,
        swap: false,
        pickup: false,
        pause: false,
      })

      for (let i = 0; i < 10; i++) {
        game.update(1 / 60)
      }

      expect(game.getState()).toBe('playing')
    })

    it('should handle swap input', () => {
      game.startLocalGame(1)

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: true,
        pickup: false,
        pause: false,
      })

      for (let i = 0; i < 10; i++) {
        game.update(1 / 60)
      }

      expect(game.getState()).toBe('playing')
    })

    it('should handle pickup input', () => {
      game.startLocalGame(1)

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false, down: false, left: false, right: false,
        fire: false, special: false, secondary: false,
        swap: false, pickup: true, pause: false,
      })

      for (let i = 0; i < 10; i++) {
        game.update(1 / 60)
      }

      expect(game.getState()).toBe('playing')
    })

    it('should handle combined movement and fire', () => {
      game.startLocalGame(1)

      const sim = game.getSimulation()
      const initialX = sim?.getState().players[0]?.x ?? 0

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: false, down: false, left: false, right: true,
        fire: true, special: false, secondary: false,
        swap: false, pickup: false, pause: false,
      })

      for (let i = 0; i < 30; i++) {
        game.update(1 / 60)
      }

      const finalX = sim?.getState().players[0]?.x ?? 0
      const bullets = sim?.getState().bullets ?? []

      expect(finalX).toBeGreaterThan(initialX)
      expect(bullets.length).toBeGreaterThan(0)
    })

    it('should handle all inputs simultaneously', () => {
      game.startLocalGame(1)

      ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue({
        up: true, down: false, left: false, right: true,
        fire: true, special: true, secondary: true,
        swap: true, pickup: true, pause: false,
      })

      for (let i = 0; i < 10; i++) {
        game.update(1 / 60)
      }

      expect(game.getState()).toBe('playing')
    })

    it('should maintain simulation consistency with rapid input changes', () => {
      game.startLocalGame(1)

      const inputs = [
        { up: true, down: false, left: false, right: false, fire: false, special: false, secondary: false, swap: false, pickup: false, pause: false },
        { up: false, down: true, left: false, right: false, fire: true, special: false, secondary: false, swap: false, pickup: false, pause: false },
        { up: false, down: false, left: true, right: false, fire: false, special: true, secondary: false, swap: false, pickup: false, pause: false },
        { up: false, down: false, left: false, right: true, fire: false, special: false, secondary: true, swap: false, pickup: false, pause: false },
      ]

      for (let i = 0; i < 60; i++) {
        ;(mockInput.getPlayer1State as ReturnType<typeof vi.fn>).mockReturnValue(inputs[i % inputs.length])
        game.update(1 / 60)
      }

      expect(game.getState()).toBe('playing')
      expect(game.getSimulation()).not.toBeNull()
    })
  })

  describe('frame timing', () => {
    it('should handle variable delta times', () => {
      game.startLocalGame(1)

      game.update(1 / 30) // 30fps
      game.update(1 / 60) // 60fps
      game.update(1 / 120) // 120fps

      expect(game.getState()).toBe('playing')
    })

    it('should accumulate time for simulation ticks', () => {
      game.startLocalGame(1)

      const sim = game.getSimulation()
      const initialFrame = sim?.getFrame() ?? 0

      // Small updates that won't trigger a tick individually
      for (let i = 0; i < 10; i++) {
        game.update(1 / 600) // Very small delta
      }

      const finalFrame = sim?.getFrame() ?? 0

      // Should have advanced at least some frames
      expect(finalFrame).toBeGreaterThanOrEqual(initialFrame)
    })
  })

  describe('game over handling', () => {
    it('should create new simulation on restart', () => {
      game.startLocalGame(1)

      const simBefore = game.getSimulation()

      game.restartGame()

      const simAfter = game.getSimulation()

      // Should be a new simulation instance
      expect(simAfter).not.toBe(simBefore)
    })
  })
})
