/**
 * HUD - 2D Canvas overlay for game UI
 *
 * Renders all HUD elements on a 2D canvas layered over the WebGL game.
 * Uses HTML5 Canvas API for crisp text and simple 2D shapes.
 * Uses Pixelon pixel font for consistent retro aesthetic.
 */

import { WEAPON_STATS, WEAPON_COLORS, AMMO_TYPE_COLORS, type WeaponType } from '../game/Weapons.ts'

export interface HUDPlayerState {
  shields: number
  maxShields: number
  lives: number
  shipLevel: number
  powerups: {
    spread: number
    laser: number
    missile: number
    orbit: number
    drone: number
    speed: number
    rapid: number
    pierce: number
  }
  weaponSlots: Array<{
    type: WeaponType
    ammo: number
    maxAmmo: number
  }>
  activeWeaponIndex: number
  maxWeaponSlots: number
}

export interface HUDGameState {
  score: number
  multiplier: number
  wave: number
  enemyCount: number
  bossActive: boolean
  bossHealth?: number
  bossMaxHealth?: number
}

export interface WeaponDropLabel {
  screenX: number
  screenY: number
  weaponType: WeaponType
}

export interface EntityHealthBar {
  screenX: number
  screenY: number
  health: number
  maxHealth: number
  width: number
}

// Color utilities
function rgbaToCSS(r: number, g: number, b: number, a: number = 1): string {
  return `rgba(${Math.round(r * 255)}, ${Math.round(g * 255)}, ${Math.round(b * 255)}, ${a})`
}

function colorToCSS(color: [number, number, number, number]): string {
  return rgbaToCSS(color[0], color[1], color[2], color[3])
}

function getHealthBarColor(ratio: number): string {
  if (ratio > 0.6) return '#0f0'
  if (ratio > 0.3) return '#ff0'
  return '#f00'
}

export class HUD {
  private canvas: HTMLCanvasElement
  private ctx: CanvasRenderingContext2D
  private width = 0
  private height = 0

  // Viewport matching WebGL's 5:3 letterbox/pillarbox
  private viewportX = 0
  private viewportY = 0
  private viewportWidth = 0
  private viewportHeight = 0

  // Design resolution (matches game world units roughly)
  private readonly DESIGN_WIDTH = 1000
  private readonly DESIGN_HEIGHT = 600

  // Font settings
  private readonly FONT_FAMILY = "'Pixelon', monospace"

  constructor() {
    this.canvas = document.createElement('canvas')
    this.canvas.id = 'hud-canvas'
    this.canvas.style.cssText = `
      position: absolute;
      top: 0;
      left: 0;
      width: 100%;
      height: 100%;
      pointer-events: none;
      z-index: 10;
      image-rendering: pixelated;
      image-rendering: crisp-edges;
      -webkit-font-smoothing: none;
      font-smooth: never;
    `

    const ctx = this.canvas.getContext('2d')
    if (!ctx) {
      throw new Error('Failed to get 2D context for HUD')
    }
    this.ctx = ctx

    // Disable anti-aliasing for sharp pixel fonts
    this.ctx.imageSmoothingEnabled = false
  }

  init(container: HTMLElement): void {
    container.appendChild(this.canvas)
  }

  resize(width: number, height: number): void {
    this.width = width
    this.height = height

    // Account for devicePixelRatio for sharp rendering on high-DPI screens
    const dpr = window.devicePixelRatio || 1
    this.canvas.width = Math.floor(width * dpr)
    this.canvas.height = Math.floor(height * dpr)

    // Scale context to match CSS pixels
    this.ctx.setTransform(dpr, 0, 0, dpr, 0, 0)

    // Re-apply anti-aliasing settings (canvas resets on resize)
    this.ctx.imageSmoothingEnabled = false

    // Calculate 5:3 viewport (match WebGL renderer)
    const targetAspect = 5 / 3
    const screenAspect = width / height

    if (screenAspect > targetAspect) {
      // Pillarbox
      this.viewportHeight = height
      this.viewportWidth = Math.floor(height * targetAspect)
      this.viewportX = Math.floor((width - this.viewportWidth) / 2)
      this.viewportY = 0
    } else {
      // Letterbox
      this.viewportWidth = width
      this.viewportHeight = Math.floor(width / targetAspect)
      this.viewportX = 0
      this.viewportY = Math.floor((height - this.viewportHeight) / 2)
    }
  }

  clear(): void {
    this.ctx.clearRect(0, 0, this.width, this.height)
  }

  /**
   * Convert design coordinates to screen coordinates
   * Design space: -500 to +500 X, -300 to +300 Y (origin center)
   */
  private toScreen(x: number, y: number): { x: number; y: number } {
    const scaleX = this.viewportWidth / this.DESIGN_WIDTH
    const scaleY = this.viewportHeight / this.DESIGN_HEIGHT

    return {
      x: this.viewportX + (x + this.DESIGN_WIDTH / 2) * scaleX,
      y: this.viewportY + (this.DESIGN_HEIGHT / 2 - y) * scaleY,
    }
  }

  /**
   * Get scale factor for consistent sizing
   */
  private getScale(): number {
    return this.viewportWidth / this.DESIGN_WIDTH
  }

  // ==========================================================================
  // Drawing Primitives
  // ==========================================================================

  private drawRect(x: number, y: number, w: number, h: number, color: string): void {
    const pos = this.toScreen(x, y)
    const scale = this.getScale()
    this.ctx.fillStyle = color
    this.ctx.fillRect(pos.x - (w * scale) / 2, pos.y - (h * scale) / 2, w * scale, h * scale)
  }

  private drawRectOutline(x: number, y: number, w: number, h: number, color: string, lineWidth: number = 2): void {
    const pos = this.toScreen(x, y)
    const scale = this.getScale()
    this.ctx.strokeStyle = color
    this.ctx.lineWidth = lineWidth * scale
    this.ctx.strokeRect(pos.x - (w * scale) / 2, pos.y - (h * scale) / 2, w * scale, h * scale)
  }

  private drawText(
    text: string,
    x: number,
    y: number,
    options: {
      size?: number
      color?: string
      align?: CanvasTextAlign
      baseline?: CanvasTextBaseline
      outline?: boolean
      outlineColor?: string
      outlineWidth?: number
    } = {}
  ): void {
    const {
      size = 14,
      color = '#fff',
      align = 'center',
      baseline = 'middle',
      outline = true,
      outlineColor = '#000',
      outlineWidth = 3,
    } = options

    const pos = this.toScreen(x, y)
    const scale = this.getScale()
    const fontSize = Math.round(size * scale)

    this.ctx.font = `${fontSize}px ${this.FONT_FAMILY}`
    this.ctx.textAlign = align
    this.ctx.textBaseline = baseline

    if (outline) {
      this.ctx.strokeStyle = outlineColor
      this.ctx.lineWidth = outlineWidth * scale
      this.ctx.lineJoin = 'round'
      this.ctx.strokeText(text, pos.x, pos.y)
    }

    this.ctx.fillStyle = color
    this.ctx.fillText(text, pos.x, pos.y)
  }

  // ==========================================================================
  // HUD Components
  // ==========================================================================

  renderPlayerHUD(player: HUDPlayerState): void {
    // Shield bar (top-left)
    const shieldX = -400
    const shieldY = 250

    // Background
    this.drawRect(shieldX, shieldY, 154, 18, 'rgba(20, 20, 30, 0.9)')
    // Border
    this.drawRectOutline(shieldX, shieldY, 152, 16, 'rgba(0, 128, 128, 0.8)')
    // Fill
    const shieldRatio = player.shields / player.maxShields
    const shieldColor = shieldRatio > 0.25 ? '#0f8' : '#f43'
    const shieldWidth = 148 * shieldRatio
    this.drawRect(shieldX - (148 - shieldWidth) / 2, shieldY, shieldWidth, 12, shieldColor)
    // Label
    this.drawText('SHIELD', shieldX - 60, shieldY, { size: 10, align: 'right' })

    // Lives (below shield)
    const livesY = 225
    this.drawText('LIVES', -475, livesY, { size: 10, align: 'left' })
    for (let i = 0; i < player.lives; i++) {
      this.drawRect(-420 + i * 20, livesY, 14, 14, '#f55')
    }

    // Ship level
    const levelY = 200
    this.drawText('LEVEL', -475, levelY, { size: 10, align: 'left' })
    for (let i = 0; i < player.shipLevel; i++) {
      this.drawRect(-420 + i * 16, levelY, 12, 12, '#ff0')
    }

    // Powerups
    const powerupY = 175
    let powerupX = -420
    const powerupConfig: Array<[keyof typeof player.powerups, string]> = [
      ['spread', '#fa0'],
      ['laser', '#0ff'],
      ['missile', '#f80'],
      ['rapid', '#f58'],
      ['pierce', '#8ff'],
      ['speed', '#88f'],
    ]

    for (const [key, color] of powerupConfig) {
      const count = player.powerups[key]
      for (let i = 0; i < count; i++) {
        this.drawRect(powerupX, powerupY, 12, 12, color)
        powerupX += 14
      }
    }

    // Weapon slots
    this.renderWeaponSlots(player)
  }

  private renderWeaponSlots(player: HUDPlayerState): void {
    const slotStartX = -420
    const slotY = 140
    const slotWidth = 70
    const slotHeight = 35
    const slotGap = 10

    for (let i = 0; i < player.maxWeaponSlots; i++) {
      const slotX = slotStartX + i * (slotWidth + slotGap)
      const weapon = player.weaponSlots[i]
      const isActive = i === player.activeWeaponIndex && weapon !== undefined

      // Slot background
      this.drawRect(slotX, slotY, slotWidth + 2, slotHeight + 2, 'rgba(20, 20, 30, 0.9)')

      // Active indicator (glowing border)
      if (isActive) {
        this.drawRectOutline(slotX, slotY, slotWidth, slotHeight, '#fff', 2)
      }

      if (weapon) {
        const stats = WEAPON_STATS[weapon.type]
        const ammoColor = AMMO_TYPE_COLORS[stats.ammoType]
        const weaponColor = WEAPON_COLORS[weapon.type]

        // Weapon name
        this.drawText(stats.name, slotX, slotY + 6, {
          size: 11,
          color: colorToCSS(weaponColor),
        })

        // Ammo bar background
        this.drawRect(slotX, slotY - 10, slotWidth - 6, 8, 'rgba(40, 40, 50, 0.9)')

        // Ammo bar fill
        const ammoRatio = weapon.ammo / weapon.maxAmmo
        const ammoBarWidth = (slotWidth - 6) * ammoRatio
        if (ammoBarWidth > 0) {
          this.drawRect(slotX - ((slotWidth - 6) - ammoBarWidth) / 2, slotY - 10, ammoBarWidth, 6, colorToCSS(ammoColor))
        }

        // Ammo count text
        this.drawText(`${weapon.ammo}`, slotX, slotY - 10, { size: 8 })
      } else {
        // Empty slot
        this.drawRect(slotX, slotY, slotWidth - 4, slotHeight - 4, 'rgba(30, 30, 40, 0.5)')
        this.drawText('EMPTY', slotX, slotY, { size: 9, color: '#444' })
      }
    }

    // Controls hint
    this.drawText('[Q] SWAP  [E] PICKUP', slotStartX + slotWidth, slotY - 28, {
      size: 8,
      color: '#666',
      align: 'left',
    })
  }

  renderGameState(state: HUDGameState): void {
    // Score (top-right)
    const scoreX = 400
    const scoreY = 260

    this.drawRect(scoreX, scoreY, 140, 35, 'rgba(20, 20, 30, 0.9)')
    this.drawText('SCORE', scoreX, scoreY + 10, { size: 10, color: '#088' })
    this.drawText(state.score.toLocaleString(), scoreX, scoreY - 5, { size: 18 })

    // Multiplier
    const multY = 220
    this.drawText(`x${state.multiplier.toFixed(1)}`, scoreX, multY, {
      size: 14,
      color: state.multiplier > 1 ? '#f0f' : '#888',
    })

    // Wave
    const waveX = 400
    const waveY = 185
    this.drawRect(waveX, waveY, 80, 25, 'rgba(20, 20, 30, 0.9)')
    this.drawText(`WAVE ${state.wave}`, waveX, waveY, { size: 12, color: '#08f' })

    // Boss health bar (top center when active)
    if (state.bossActive && state.bossHealth !== undefined && state.bossMaxHealth !== undefined) {
      this.renderBossHealth(state.bossHealth, state.bossMaxHealth)
    }
  }

  private renderBossHealth(health: number, maxHealth: number): void {
    const barX = 0
    const barY = 260
    const barWidth = 300
    const barHeight = 20

    // Warning pulse
    const pulse = Math.sin(Date.now() / 200) * 0.2 + 0.8

    // Background
    this.drawRect(barX, barY, barWidth + 4, barHeight + 4, `rgba(60, 0, 0, ${pulse * 0.9})`)

    // Border
    this.drawRectOutline(barX, barY, barWidth + 2, barHeight + 2, `rgba(255, 0, 0, ${pulse})`, 2)

    // Health fill
    const healthRatio = health / maxHealth
    const healthWidth = barWidth * healthRatio
    this.drawRect(barX - (barWidth - healthWidth) / 2, barY, healthWidth, barHeight - 4, `rgba(255, 0, 0, ${pulse})`)

    // Label
    this.drawText('WARNING', barX, barY + 25, { size: 12, color: `rgba(255, 0, 0, ${pulse})` })
  }

  /**
   * Convert world-projected coordinates to canvas pixel coordinates.
   * worldToScreen returns coords where X is -500 to +500, Y is -300 to +300 (Y+ is up).
   * Canvas has Y+ pointing down, so we need to flip Y.
   */
  private worldToCanvas(worldScreenX: number, worldScreenY: number): { x: number; y: number } {
    const scaleX = this.viewportWidth / this.DESIGN_WIDTH
    const scaleY = this.viewportHeight / this.DESIGN_HEIGHT

    return {
      x: this.viewportX + (worldScreenX + this.DESIGN_WIDTH / 2) * scaleX,
      y: this.viewportY + (this.DESIGN_HEIGHT / 2 - worldScreenY) * scaleY,
    }
  }

  renderWeaponDropLabels(drops: WeaponDropLabel[]): void {
    for (const drop of drops) {
      const stats = WEAPON_STATS[drop.weaponType]
      const ammoColor = AMMO_TYPE_COLORS[stats.ammoType]

      // Convert from world-projected coordinates to canvas pixels
      const pos = this.worldToCanvas(drop.screenX, drop.screenY)
      const scale = this.getScale()
      const x = pos.x
      const y = pos.y

      // Background pill
      const textWidth = stats.name.length * 8 * scale + 12 * scale
      const textHeight = 18 * scale

      this.ctx.fillStyle = 'rgba(15, 15, 25, 0.9)'
      this.roundRect(x - textWidth / 2, y - textHeight / 2, textWidth, textHeight, 4 * scale)
      this.ctx.fill()

      // Ammo type indicator bar
      this.ctx.fillStyle = colorToCSS(ammoColor)
      this.ctx.fillRect(x - textWidth / 2 + 2 * scale, y + textHeight / 2 - 4 * scale, textWidth - 4 * scale, 2 * scale)

      // Weapon name
      const fontSize = Math.round(11 * scale)
      this.ctx.font = `${fontSize}px ${this.FONT_FAMILY}`
      this.ctx.textAlign = 'center'
      this.ctx.textBaseline = 'middle'

      // Outline
      this.ctx.strokeStyle = '#000'
      this.ctx.lineWidth = 3 * scale
      this.ctx.lineJoin = 'round'
      this.ctx.strokeText(stats.name, x, y - 1 * scale)

      // Fill
      this.ctx.fillStyle = '#fff'
      this.ctx.fillText(stats.name, x, y - 1 * scale)
    }
  }

  renderEntityHealthBars(bars: EntityHealthBar[]): void {
    const scale = this.getScale()

    for (const bar of bars) {
      const { screenX, screenY, health, maxHealth, width } = bar
      // Convert from world-projected coordinates to canvas pixels
      const pos = this.worldToCanvas(screenX, screenY)
      const x = pos.x
      const y = pos.y
      const barWidth = width * scale
      const barHeight = 6 * scale

      const healthRatio = health / maxHealth

      // Background
      this.ctx.fillStyle = 'rgba(30, 30, 30, 0.8)'
      this.ctx.fillRect(x - barWidth / 2 - 2, y - barHeight / 2 - 2, barWidth + 4, barHeight + 4)

      // Health fill
      const fillWidth = barWidth * healthRatio
      this.ctx.fillStyle = getHealthBarColor(healthRatio)
      this.ctx.fillRect(x - barWidth / 2, y - barHeight / 2, fillWidth, barHeight)
    }
  }

  private roundRect(x: number, y: number, w: number, h: number, r: number): void {
    this.ctx.beginPath()
    this.ctx.moveTo(x + r, y)
    this.ctx.lineTo(x + w - r, y)
    this.ctx.quadraticCurveTo(x + w, y, x + w, y + r)
    this.ctx.lineTo(x + w, y + h - r)
    this.ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h)
    this.ctx.lineTo(x + r, y + h)
    this.ctx.quadraticCurveTo(x, y + h, x, y + h - r)
    this.ctx.lineTo(x, y + r)
    this.ctx.quadraticCurveTo(x, y, x + r, y)
    this.ctx.closePath()
  }
}
