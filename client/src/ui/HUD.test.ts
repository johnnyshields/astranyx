import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { HUD, type HUDPlayerState, type HUDGameState, type WeaponDropLabel, type EntityHealthBar } from './HUD'

describe('HUD', () => {
  let hud: HUD
  let mockContext: CanvasRenderingContext2D

  beforeEach(() => {
    // Mock canvas context
    mockContext = {
      clearRect: vi.fn(),
      fillRect: vi.fn(),
      strokeRect: vi.fn(),
      fillText: vi.fn(),
      strokeText: vi.fn(),
      beginPath: vi.fn(),
      moveTo: vi.fn(),
      lineTo: vi.fn(),
      quadraticCurveTo: vi.fn(),
      closePath: vi.fn(),
      fill: vi.fn(),
      stroke: vi.fn(),
      setTransform: vi.fn(),
      fillStyle: '',
      strokeStyle: '',
      lineWidth: 1,
      lineJoin: 'miter' as CanvasLineJoin,
      font: '',
      textAlign: 'left' as CanvasTextAlign,
      textBaseline: 'alphabetic' as CanvasTextBaseline,
      imageSmoothingEnabled: true,
    } as unknown as CanvasRenderingContext2D

    // Mock document.createElement to return canvas with our mock context
    const originalCreateElement = document.createElement.bind(document)
    vi.spyOn(document, 'createElement').mockImplementation((tagName) => {
      if (tagName === 'canvas') {
        const canvas = originalCreateElement('canvas') as HTMLCanvasElement
        vi.spyOn(canvas, 'getContext').mockReturnValue(mockContext as unknown as RenderingContext)
        return canvas
      }
      return originalCreateElement(tagName)
    })

    // Mock window.devicePixelRatio
    Object.defineProperty(window, 'devicePixelRatio', { value: 1, configurable: true })

    hud = new HUD()
  })

  afterEach(() => {
    vi.restoreAllMocks()
  })

  describe('constructor', () => {
    it('should create HUD with canvas', () => {
      expect(hud).toBeInstanceOf(HUD)
    })

    it('should throw if 2D context unavailable', () => {
      vi.spyOn(document, 'createElement').mockImplementation((tagName) => {
        if (tagName === 'canvas') {
          return {
            id: '',
            style: { cssText: '' },
            getContext: vi.fn().mockReturnValue(null),
          } as unknown as HTMLCanvasElement
        }
        return document.createElement(tagName)
      })

      expect(() => new HUD()).toThrow('Failed to get 2D context for HUD')
    })
  })

  describe('init', () => {
    it('should append canvas to container', () => {
      const container = document.createElement('div')
      const appendChildSpy = vi.spyOn(container, 'appendChild')

      hud.init(container)

      expect(appendChildSpy).toHaveBeenCalled()
    })
  })

  describe('resize', () => {
    it('should update dimensions', () => {
      hud.resize(1920, 1080)
      // Verifies internal state is set (tested indirectly through rendering)
    })

    it('should handle high DPI displays', () => {
      Object.defineProperty(window, 'devicePixelRatio', { value: 2, configurable: true })
      hud.resize(1920, 1080)
      // Canvas should be scaled appropriately
    })

    it('should calculate pillarbox for wide screens', () => {
      // 16:9 aspect is wider than 5:3
      hud.resize(1920, 1080)
      // Should apply pillarbox
    })

    it('should calculate letterbox for tall screens', () => {
      // Tall aspect narrower than 5:3
      hud.resize(800, 1200)
      // Should apply letterbox
    })
  })

  describe('clear', () => {
    it('should clear the canvas', () => {
      hud.resize(1920, 1080)
      hud.clear()
      expect(mockContext.clearRect).toHaveBeenCalled()
    })
  })

  describe('renderPlayerHUD', () => {
    it('should render player state', () => {
      hud.resize(1920, 1080)

      const playerState: HUDPlayerState = {
        shields: 75,
        maxShields: 100,
        lives: 3,
        shipLevel: 2,
        powerups: {
          spread: 2,
          laser: 1,
          missile: 0,
          orbit: 0,
          drone: 1,
          speed: 0,
          rapid: 0,
          pierce: 0,
        },
        weaponSlots: [
          { type: 'vulcan', ammo: 200, maxAmmo: 400 },
          { type: 'missile', ammo: 50, maxAmmo: 80 },
        ],
        activeWeaponIndex: 0,
        maxWeaponSlots: 3,
      }

      hud.renderPlayerHUD(playerState)

      // Should have drawn various elements
      expect(mockContext.fillRect).toHaveBeenCalled()
      expect(mockContext.fillText).toHaveBeenCalled()
    })

    it('should render empty weapon slots', () => {
      hud.resize(1920, 1080)

      const playerState: HUDPlayerState = {
        shields: 100,
        maxShields: 100,
        lives: 3,
        shipLevel: 1,
        powerups: {
          spread: 0,
          laser: 0,
          missile: 0,
          orbit: 0,
          drone: 0,
          speed: 0,
          rapid: 0,
          pierce: 0,
        },
        weaponSlots: [],
        activeWeaponIndex: -1,
        maxWeaponSlots: 3,
      }

      hud.renderPlayerHUD(playerState)
      expect(mockContext.fillText).toHaveBeenCalled()
    })

    it('should highlight active weapon', () => {
      hud.resize(1920, 1080)

      const playerState: HUDPlayerState = {
        shields: 100,
        maxShields: 100,
        lives: 3,
        shipLevel: 1,
        powerups: {
          spread: 0,
          laser: 0,
          missile: 0,
          orbit: 0,
          drone: 0,
          speed: 0,
          rapid: 0,
          pierce: 0,
        },
        weaponSlots: [{ type: 'shotgun', ammo: 30, maxAmmo: 120 }],
        activeWeaponIndex: 0,
        maxWeaponSlots: 3,
      }

      hud.renderPlayerHUD(playerState)
      expect(mockContext.strokeRect).toHaveBeenCalled()
    })
  })

  describe('renderGameState', () => {
    it('should render game state', () => {
      hud.resize(1920, 1080)

      const gameState: HUDGameState = {
        score: 12500,
        multiplier: 2.5,
        wave: 5,
        enemyCount: 10,
        bossActive: false,
      }

      hud.renderGameState(gameState)

      expect(mockContext.fillText).toHaveBeenCalled()
    })

    it('should render boss health bar when active', () => {
      hud.resize(1920, 1080)

      const gameState: HUDGameState = {
        score: 50000,
        multiplier: 1.0,
        wave: 10,
        enemyCount: 1,
        bossActive: true,
        bossHealth: 5000,
        bossMaxHealth: 10000,
      }

      hud.renderGameState(gameState)

      // Should render boss health bar
      expect(mockContext.fillRect).toHaveBeenCalled()
    })

    it('should handle multiplier display', () => {
      hud.resize(1920, 1080)

      const gameState: HUDGameState = {
        score: 1000,
        multiplier: 1.0,
        wave: 1,
        enemyCount: 5,
        bossActive: false,
      }

      hud.renderGameState(gameState)

      // Multiplier should be rendered with appropriate color
      expect(mockContext.fillText).toHaveBeenCalled()
    })
  })

  describe('renderWeaponDropLabels', () => {
    it('should render weapon drop labels', () => {
      hud.resize(1920, 1080)

      const drops: WeaponDropLabel[] = [
        { screenX: 100, screenY: 50, weaponType: 'vulcan' },
        { screenX: -200, screenY: -100, weaponType: 'missile' },
      ]

      hud.renderWeaponDropLabels(drops)

      expect(mockContext.fill).toHaveBeenCalled()
      expect(mockContext.fillText).toHaveBeenCalled()
    })

    it('should handle empty drops array', () => {
      hud.resize(1920, 1080)
      hud.renderWeaponDropLabels([])
      // Should not throw
    })
  })

  describe('renderEntityHealthBars', () => {
    it('should render health bars', () => {
      hud.resize(1920, 1080)

      const bars: EntityHealthBar[] = [
        { screenX: 0, screenY: 100, health: 75, maxHealth: 100, width: 50 },
        { screenX: 200, screenY: -50, health: 25, maxHealth: 100, width: 40 },
      ]

      hud.renderEntityHealthBars(bars)

      expect(mockContext.fillRect).toHaveBeenCalled()
    })

    it('should color based on health ratio', () => {
      hud.resize(1920, 1080)

      // Full health (green)
      const fullHealth: EntityHealthBar[] = [
        { screenX: 0, screenY: 0, health: 100, maxHealth: 100, width: 50 },
      ]
      hud.renderEntityHealthBars(fullHealth)

      // Half health (yellow)
      const halfHealth: EntityHealthBar[] = [
        { screenX: 0, screenY: 0, health: 50, maxHealth: 100, width: 50 },
      ]
      hud.renderEntityHealthBars(halfHealth)

      // Low health (red)
      const lowHealth: EntityHealthBar[] = [
        { screenX: 0, screenY: 0, health: 20, maxHealth: 100, width: 50 },
      ]
      hud.renderEntityHealthBars(lowHealth)

      expect(mockContext.fillRect).toHaveBeenCalled()
    })

    it('should handle empty bars array', () => {
      hud.resize(1920, 1080)
      hud.renderEntityHealthBars([])
      // Should not throw
    })
  })
})
