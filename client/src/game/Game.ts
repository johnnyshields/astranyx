import type { Renderer } from '../core/Renderer.ts'
import type { Input } from '../core/Input.ts'
import { Simulation, type EnemyType, type BulletType, type PowerupType, type BossType } from './Simulation.ts'
import { LockstepNetcode, type PlayerInput } from '../network/LockstepNetcode.ts'

export type GameState = 'title' | 'lobby' | 'connecting' | 'playing' | 'paused' | 'gameover'

// Color definitions
const COLORS = {
  // Player colors
  player1: [0.0, 1.0, 1.0, 1.0] as [number, number, number, number],    // Cyan
  player2: [1.0, 0.5, 0.0, 1.0] as [number, number, number, number],    // Orange

  // Bullet colors
  shot: [0.0, 1.0, 1.0, 1.0] as [number, number, number, number],       // Cyan
  spread: [1.0, 0.7, 0.0, 1.0] as [number, number, number, number],     // Orange
  laser: [0.0, 1.0, 1.0, 1.0] as [number, number, number, number],      // Cyan
  mega: [1.0, 1.0, 0.0, 1.0] as [number, number, number, number],       // Yellow
  missile: [1.0, 0.5, 0.0, 1.0] as [number, number, number, number],    // Orange
  drone: [0.5, 1.0, 0.5, 1.0] as [number, number, number, number],      // Light green
  enemy: [1.0, 0.2, 0.2, 1.0] as [number, number, number, number],      // Red
  aimed: [1.0, 0.4, 0.0, 1.0] as [number, number, number, number],      // Orange-red
  big: [1.0, 0.0, 0.0, 1.0] as [number, number, number, number],        // Red
  ring: [1.0, 0.0, 1.0, 1.0] as [number, number, number, number],       // Magenta

  // Enemy colors
  grunt: [0.6, 0.2, 0.2, 1.0] as [number, number, number, number],
  shooter: [0.7, 0.3, 0.1, 1.0] as [number, number, number, number],
  swerver: [0.5, 0.3, 0.5, 1.0] as [number, number, number, number],
  tank: [0.3, 0.4, 0.3, 1.0] as [number, number, number, number],
  speeder: [0.4, 0.4, 0.6, 1.0] as [number, number, number, number],
  bomber: [0.5, 0.2, 0.1, 1.0] as [number, number, number, number],
  sniper: [0.2, 0.3, 0.5, 1.0] as [number, number, number, number],
  carrier: [0.3, 0.3, 0.4, 1.0] as [number, number, number, number],
  mine: [0.6, 0.0, 0.0, 1.0] as [number, number, number, number],
  spiral: [0.4, 0.1, 0.5, 1.0] as [number, number, number, number],
  shield: [0.2, 0.5, 0.2, 1.0] as [number, number, number, number],
  splitter: [0.5, 0.4, 0.2, 1.0] as [number, number, number, number],

  // Powerup colors
  SHIELD: [0.0, 1.0, 0.5, 1.0] as [number, number, number, number],
  UPGRADE: [1.0, 1.0, 0.0, 1.0] as [number, number, number, number],
  SPREAD: [1.0, 0.7, 0.0, 1.0] as [number, number, number, number],
  LASER: [0.0, 1.0, 1.0, 1.0] as [number, number, number, number],
  MISSILE: [1.0, 0.5, 0.0, 1.0] as [number, number, number, number],
  ORBIT: [1.0, 0.0, 1.0, 1.0] as [number, number, number, number],
  DRONE: [0.5, 1.0, 0.5, 1.0] as [number, number, number, number],
  SPEED: [0.5, 0.5, 1.0, 1.0] as [number, number, number, number],
  RAPID: [1.0, 0.3, 0.5, 1.0] as [number, number, number, number],
  PIERCE: [0.5, 1.0, 1.0, 1.0] as [number, number, number, number],
  LIFE: [1.0, 0.3, 0.3, 1.0] as [number, number, number, number],

  // Explosion colors
  explosion: [
    [1.0, 1.0, 1.0, 1.0] as [number, number, number, number],
    [1.0, 1.0, 0.0, 1.0] as [number, number, number, number],
    [1.0, 0.5, 0.0, 1.0] as [number, number, number, number],
    [1.0, 0.0, 0.0, 1.0] as [number, number, number, number],
    [0.5, 0.0, 0.0, 1.0] as [number, number, number, number],
  ],

  // Boss colors
  boss: [
    [0.3, 0.2, 0.4, 1.0] as [number, number, number, number], // CLASSIC
    [0.2, 0.4, 0.2, 1.0] as [number, number, number, number], // TWIN
    [0.3, 0.3, 0.4, 1.0] as [number, number, number, number], // CARRIER
    [0.4, 0.2, 0.2, 1.0] as [number, number, number, number], // LASER
    [0.3, 0.3, 0.4, 1.0] as [number, number, number, number], // WALL
    [0.3, 0.1, 0.3, 1.0] as [number, number, number, number], // FINAL
  ],
}

export class Game {
  private renderer: Renderer
  private input: Input
  private state: GameState = 'title'

  // Multiplayer
  private simulation: Simulation | null = null
  private netcode: LockstepNetcode | null = null
  private localPlayerId: string = ''
  private playerIds: string[] = []

  // Single player fallback
  private singlePlayerMode = true

  private screenWidth = 0
  private screenHeight = 0

  // Starfield background
  private stars: Array<{ x: number; y: number; z: number; speed: number }> = []

  // Rendering interpolation
  private lastState: ReturnType<Simulation['getState']> | null = null
  private currentState: ReturnType<Simulation['getState']> | null = null

  // Screen shake tracking
  private shakeOffset = { x: 0, y: 0 }

  constructor(renderer: Renderer, input: Input) {
    this.renderer = renderer
    this.input = input
  }

  async init(): Promise<void> {
    // Initialize starfield
    for (let i = 0; i < 200; i++) {
      this.stars.push({
        x: (Math.random() - 0.5) * 2000,
        y: (Math.random() - 0.5) * 1200,
        z: Math.random() * 500 - 600,
        speed: Math.random() * 100 + 50,
      })
    }

    // Auto-start single player for now
    this.startSinglePlayer()

    console.log('Game initialized')
  }

  startSinglePlayer(): void {
    this.singlePlayerMode = true
    this.localPlayerId = 'player_local'
    this.playerIds = [this.localPlayerId]

    this.simulation = new Simulation(this.playerIds)
    this.state = 'playing'

    console.log('Single player mode started')
  }

  startMultiplayer(
    localPlayerId: string,
    playerIds: string[],
    _playerOrder: Map<string, number>,
    netcode: LockstepNetcode
  ): void {
    this.singlePlayerMode = false
    this.localPlayerId = localPlayerId
    this.playerIds = playerIds
    this.netcode = netcode

    // All players use same seed for determinism
    const seed = 12345
    this.simulation = new Simulation(playerIds, seed)

    // Set up netcode input handler
    netcode.setInputHandler((inputs) => {
      this.simulation?.tick(inputs)
      this.lastState = this.currentState
      this.currentState = this.simulation?.getState() ?? null
    })

    netcode.start()
    this.state = 'playing'

    console.log('Multiplayer mode started with players:', playerIds)
  }

  resize(width: number, height: number): void {
    this.screenWidth = width
    this.screenHeight = height
  }

  update(dt: number): void {
    const inputState = this.input.getState()

    // Handle pause
    if (inputState.pause && this.state === 'playing') {
      this.state = 'paused'
    } else if (inputState.pause && this.state === 'paused') {
      this.state = 'playing'
    }

    if (this.state !== 'playing') {
      this.input.clearFrameState()
      return
    }

    // Get current input
    const currentInput: PlayerInput = {
      up: inputState.up,
      down: inputState.down,
      left: inputState.left,
      right: inputState.right,
      fire: inputState.fire,
      special: inputState.special,
    }

    if (this.singlePlayerMode) {
      // Single player: immediate simulation
      const inputs = new Map<string, PlayerInput>()
      inputs.set(this.localPlayerId, currentInput)

      this.lastState = this.currentState
      this.simulation?.tick(inputs)
      this.currentState = this.simulation?.getState() ?? null
    } else {
      // Multiplayer: lockstep
      this.netcode?.tick(currentInput)
    }

    // Update starfield
    for (const star of this.stars) {
      star.x -= star.speed * dt

      if (star.x < -1000) {
        star.x = 1000
        star.y = (Math.random() - 0.5) * 1200
      }
    }

    // Check game over
    if (this.currentState?.gameOver) {
      this.state = 'gameover'
    }

    this.input.clearFrameState()
  }

  render(_alpha: number): void {
    const state = this.currentState

    // Calculate screen shake
    if (state && state.screenShake > 0) {
      this.shakeOffset.x = (Math.random() - 0.5) * state.screenShake * 20
      this.shakeOffset.y = (Math.random() - 0.5) * state.screenShake * 20
    } else {
      this.shakeOffset.x = 0
      this.shakeOffset.y = 0
    }

    this.renderer.beginFrame(1 / 60)

    // Draw starfield (not affected by shake)
    for (const star of this.stars) {
      const brightness = (star.z + 600) / 500
      const size = 1 + brightness * 2
      this.renderer.drawQuad(
        star.x, star.y, star.z,
        size, size,
        [brightness * 0.8, brightness * 0.9, brightness, 1]
      )
    }

    // Draw game entities with screen shake
    if (state) {
      // Particles (background layer)
      for (const particle of state.particles) {
        this.renderParticle(particle)
      }

      // Powerups
      for (const powerup of state.powerups) {
        this.renderPowerup(powerup)
      }

      // Enemy bullets
      for (const bullet of state.bullets) {
        if (bullet.isEnemy) {
          this.renderBullet(bullet)
        }
      }

      // Player bullets
      for (const bullet of state.bullets) {
        if (!bullet.isEnemy) {
          this.renderBullet(bullet)
        }
      }

      // Beams
      for (const beam of state.beams) {
        this.renderBeam(beam)
      }

      // Missiles
      for (const missile of state.missiles) {
        this.renderMissile(missile)
      }

      // Enemies
      for (const enemy of state.enemies) {
        this.renderEnemy(enemy)
      }

      // Boss
      if (state.boss) {
        this.renderBoss(state.boss)
      }

      // Players
      for (const player of state.players) {
        this.renderPlayer(player)
      }

      // Draw HUD
      this.renderHUD(state)
    }

    // Draw pause overlay
    if (this.state === 'paused') {
      this.renderer.drawQuad(0, 0, 100, 2000, 1200, [0, 0, 0.1, 0.8])
    }

    // Draw game over overlay
    if (this.state === 'gameover') {
      this.renderer.drawQuad(0, 0, 100, 2000, 1200, [0.1, 0, 0, 0.9])
    }

    // Show waiting indicator in multiplayer
    if (!this.singlePlayerMode && this.netcode?.isWaitingForInputs()) {
      this.renderer.drawQuad(0, 200, 100, 200, 30, [1, 0.5, 0, 0.8])
    }

    this.renderer.endFrame()
  }

  // ==========================================================================
  // Entity Renderers
  // ==========================================================================

  private renderPlayer(player: ReturnType<Simulation['getState']>['players'][0]): void {
    if (player.dead) return

    // Invincibility flash
    if (player.invincible > 0 && Math.floor(player.invincible / 4) % 2 === 0) return

    const x = player.x + this.shakeOffset.x
    const y = player.y + this.shakeOffset.y
    const isLocal = player.playerId === this.localPlayerId
    const lvl = player.shipLevel - 1

    // Draw orbs
    for (const orb of player.orbs) {
      const ox = x + Math.cos(orb.angle) * orb.radius
      const oy = y + Math.sin(orb.angle) * orb.radius

      // Orb glow
      this.renderer.drawQuad(ox, oy, -1, 18, 18, [1, 0, 1, 0.2])
      // Orb core
      this.renderer.drawQuad(ox, oy, 0, 10, 10, [1, 0, 1, 1])
      this.renderer.drawQuad(ox, oy, 1, 4, 4, [1, 1, 1, 1])
    }

    // Draw drones
    for (const drone of player.drones) {
      this.renderer.drawQuad(drone.x, drone.y, 0, 14, 10, [0.5, 1, 0.5, 1])
      this.renderer.drawQuad(drone.x + 4, drone.y, 1, 6, 4, [1, 1, 1, 1])
    }

    const color = isLocal ? COLORS.player1 : COLORS.player2
    const rotation = -player.vy * 0.002
    const clampedRotation = Math.max(-0.4, Math.min(0.4, rotation))

    // Ship size scales with level
    const bodyWidth = 44 + lvl * 10
    const bodyHeight = 20 + lvl * 4

    // Engine exhaust (animated)
    const exhaustLength = 30 + Math.sin(player.chargeTime * 20) * 5
    this.renderer.drawQuad(x - bodyWidth/2 - exhaustLength/2, y, -1, exhaustLength, 10, [0.2, 0.5, 1.0, 0.5], clampedRotation)
    this.renderer.drawQuad(x - bodyWidth/2 - exhaustLength/3, y, -0.5, exhaustLength/2, 6, [0.5, 0.8, 1.0, 0.8], clampedRotation)

    // Main body
    this.renderer.drawQuad(x, y, 0, bodyWidth, bodyHeight, [0.6, 0.65, 0.75, 1.0], clampedRotation)

    // Cockpit
    this.renderer.drawQuad(x + bodyWidth/4, y, 1, bodyWidth/4, bodyHeight * 0.5, color, clampedRotation)

    // Wings
    const wingWidth = 35 + lvl * 5
    const wingHeight = 8 + lvl * 2
    this.renderer.drawQuad(x - 5, y + bodyHeight/2 + wingHeight/2, 0, wingWidth, wingHeight, [0.5, 0.55, 0.65, 1.0], clampedRotation * 1.2)
    this.renderer.drawQuad(x - 5, y - bodyHeight/2 - wingHeight/2, 0, wingWidth, wingHeight, [0.5, 0.55, 0.65, 1.0], clampedRotation * 1.2)

    // Wing tips (red)
    this.renderer.drawQuad(x - bodyWidth/3, y + bodyHeight/2 + wingHeight, 0.5, 12, 4, [1.0, 0.3, 0.2, 1.0], clampedRotation)
    this.renderer.drawQuad(x - bodyWidth/3, y - bodyHeight/2 - wingHeight, 0.5, 12, 4, [1.0, 0.3, 0.2, 1.0], clampedRotation)

    // Charge indicator
    if (player.charging) {
      const chargeSize = Math.min(player.chargeTime * 30, 24)
      this.renderer.drawQuad(x + bodyWidth/2 + 10, y, 2, chargeSize, chargeSize, [...color.slice(0, 3), 0.5 + Math.sin(Date.now() / 50) * 0.3] as [number, number, number, number])
    }

    // Invincibility shield
    if (player.invincible > 0 && player.invincible < 30) {
      this.renderer.drawQuad(x, y, -2, bodyWidth + 20, bodyHeight + 20, [...color.slice(0, 3), player.invincible / 60] as [number, number, number, number])
    }
  }

  private renderEnemy(enemy: ReturnType<Simulation['getState']>['enemies'][0]): void {
    const x = enemy.x + this.shakeOffset.x
    const y = enemy.y + this.shakeOffset.y
    const color = COLORS[enemy.type as keyof typeof COLORS] as [number, number, number, number] || COLORS.grunt

    // Size varies by enemy type
    let width = 40
    let height = 25

    switch (enemy.type) {
      case 'grunt':
        width = 30; height = 20
        break
      case 'shooter':
        width = 35; height = 25
        break
      case 'swerver':
        width = 28; height = 18
        break
      case 'tank':
        width = 60; height = 40
        break
      case 'speeder':
        width = 35; height = 15
        break
      case 'bomber':
        width = 45; height = 35
        break
      case 'sniper':
        width = 40; height = 20
        break
      case 'carrier':
        width = 70; height = 50
        break
      case 'mine':
        width = 25; height = 25
        break
      case 'spiral':
        width = 45; height = 30
        break
      case 'shield':
        width = 50; height = 35
        break
      case 'splitter':
        width = 40; height = 30
        break
    }

    // Shield effect
    if (enemy.hasShield) {
      this.renderer.drawQuad(x, y, -1, width + 15, height + 15, [0, 0.8, 0.2, 0.3])
    }

    // Enemy glow
    this.renderer.drawQuad(x, y, -1, width + 10, height + 10, [color[0], color[1], color[2], 0.2])

    // Main body
    this.renderer.drawQuad(x, y, 0, width, height, color)

    // Core (lighter)
    this.renderer.drawQuad(x - width/6, y, 0.5, width/2, height * 0.6, [color[0] + 0.2, color[1] + 0.2, color[2] + 0.2, 1])

    // Health bar
    const healthRatio = enemy.health / enemy.maxHealth
    const barWidth = width
    this.renderer.drawQuad(x, y - height/2 - 8, 2, barWidth + 2, 6, [0.2, 0.2, 0.2, 0.8])
    const healthColor: [number, number, number, number] = healthRatio > 0.5
      ? [0, 0.8, 0.5, 1]
      : healthRatio > 0.25
        ? [1, 1, 0, 1]
        : [1, 0.3, 0.2, 1]
    this.renderer.drawQuad(x - (1 - healthRatio) * barWidth / 2, y - height/2 - 8, 3, barWidth * healthRatio, 4, healthColor)
  }

  private renderBoss(boss: ReturnType<Simulation['getState']>['boss']): void {
    if (!boss) return

    const x = boss.x + this.shakeOffset.x
    const y = boss.y + this.shakeOffset.y
    const color = COLORS.boss[boss.type] ?? COLORS.boss[0]!

    // Boss sizes vary by type
    const sizes = [
      { w: 80, h: 70 },   // CLASSIC
      { w: 70, h: 50 },   // TWIN
      { w: 100, h: 80 },  // CARRIER
      { w: 80, h: 60 },   // LASER
      { w: 60, h: 160 },  // WALL
      { w: 110, h: 100 }, // FINAL
    ]
    const size = sizes[boss.type] ?? sizes[0]!

    // Boss glow
    const pulse = Math.sin(Date.now() / 200) * 5
    this.renderer.drawQuad(x, y, -2, size.w + 30 + pulse, size.h + 30 + pulse, [color[0], color[1], color[2], 0.15])

    // Main body
    this.renderer.drawQuad(x, y, 0, size.w, size.h, color)
    this.renderer.drawQuad(x, y, 0.5, size.w * 0.8, size.h * 0.8, [color[0] + 0.1, color[1] + 0.1, color[2] + 0.1, 1])

    // Type-specific rendering
    switch (boss.type) {
      case 0: // CLASSIC - Core
        {
          const coreColor: [number, number, number, number] = boss.health / boss.maxHealth > 0.5
            ? [1, 1, 0, 1]
            : boss.health / boss.maxHealth > 0.25
              ? [1, 0.5, 0, 1]
              : [1, 0, 0, 1]
          this.renderer.drawQuad(x, y, 1, 30 + pulse, 30 + pulse, coreColor)
        }
        break

      case 1: // TWIN
        // Second body
        if (boss.twin) {
          this.renderer.drawQuad(x, boss.twin.y + this.shakeOffset.y, 0, 50, 40, color)
          this.renderer.drawQuad(x, boss.twin.y + this.shakeOffset.y, 1, 20, 20, [0, 1, 0, 1])
        }
        this.renderer.drawQuad(x, y, 1, 20, 20, [0, 1, 0, 1])
        break

      case 2: // CARRIER
        // Hangar bay
        this.renderer.drawQuad(x + 20, y, 1, 20, size!.h * 0.6, [1, 1, 0, 0.8])
        break

      case 3: // LASER
        // Laser barrel
        this.renderer.drawQuad(x - size!.w/2 - 30, y, 0.5, 50, 16, [0.5, 0.5, 0.5, 1])
        if (boss.charging) {
          const chargeSize = (boss.chargeTime || 0) * 15
          this.renderer.drawQuad(x - size!.w/2 - 50, y, 1, chargeSize, chargeSize, [1, 0, 0, 0.5 + Math.sin(Date.now() / 50) * 0.3])
        }
        break

      case 4: // WALL
        // Segments
        if (boss.segments) {
          for (const seg of boss.segments) {
            const segColor: [number, number, number, number] = seg.hp > 0 ? [0.5, 0.5, 0.6, 1] : [0.2, 0.2, 0.2, 1]
            this.renderer.drawQuad(x - 20, y + seg.y, 0.5, 40, 28, segColor)
            if (seg.hp > 0) {
              this.renderer.drawQuad(x - 30, y + seg.y, 1, 10, 8, [1, 0.3, 0.3, 1])
            }
          }
        }
        break

      case 5: // FINAL
        // Core with pulsing
        const finalCoreColor: [number, number, number, number] = boss.health / boss.maxHealth > 0.5
          ? [1, 0, 1, 1]
          : boss.health / boss.maxHealth > 0.25
            ? [1, 0, 0.5, 1]
            : [1, 0, 0, 1]
        this.renderer.drawQuad(x, y, 1, 40 + pulse, 40 + pulse, finalCoreColor)
        this.renderer.drawQuad(x, y, 2, 16, 16, [1, 1, 1, 1])
        // Cannons
        this.renderer.drawQuad(x - size!.w/2 - 10, y - 15, 0.5, 25, 10, [1, 0.3, 0.3, 1])
        this.renderer.drawQuad(x - size!.w/2 - 10, y + 15, 0.5, 25, 10, [1, 0.3, 0.3, 1])
        break
    }

    // Health bar
    const healthRatio = boss.health / boss.maxHealth
    const barWidth = 100
    this.renderer.drawQuad(x, y - size!.h/2 - 15, 2, barWidth + 4, 12, [0.2, 0.2, 0.2, 0.8])
    const healthColor: [number, number, number, number] = healthRatio > 0.5
      ? [0, 0.8, 0.5, 1]
      : healthRatio > 0.25
        ? [1, 1, 0, 1]
        : [1, 0.3, 0.2, 1]
    this.renderer.drawQuad(x - (1 - healthRatio) * barWidth / 2, y - size!.h/2 - 15, 3, barWidth * healthRatio, 8, healthColor)
  }

  private renderBullet(bullet: ReturnType<Simulation['getState']>['bullets'][0]): void {
    const x = bullet.x + this.shakeOffset.x
    const y = bullet.y + this.shakeOffset.y

    let color = COLORS[bullet.type as keyof typeof COLORS] as [number, number, number, number] || COLORS.shot
    let width = 15
    let height = 4

    switch (bullet.type) {
      case 'shot':
        width = 15; height = 4
        break
      case 'spread':
        width = 12; height = 4
        break
      case 'laser':
        width = 25; height = 3
        color = [0, 1, 1, 1]
        break
      case 'mega':
        width = 30; height = 15
        break
      case 'drone':
        width = 10; height = 3
        break
      case 'enemy':
        width = 10; height = 6
        break
      case 'aimed':
        width = 12; height = 5
        break
      case 'big':
        width = 20; height = 20
        break
      case 'ring':
        width = 8; height = 8
        break
    }

    // Bullet glow
    this.renderer.drawQuad(x, y, -0.5, width + 8, height + 8, [color[0], color[1], color[2], 0.3])
    // Bullet core
    this.renderer.drawQuad(x, y, 0, width, height, color)
  }

  private renderBeam(beam: ReturnType<Simulation['getState']>['beams'][0]): void {
    const x = beam.x + this.shakeOffset.x
    const y = beam.y + this.shakeOffset.y
    const beamHeight = 8 + beam.power * 4

    // Beam glow
    this.renderer.drawQuad(x + beam.width/2, y, -1, beam.width, beamHeight + 20, [0, 1, 1, 0.2])
    // Beam core
    this.renderer.drawQuad(x + beam.width/2, y, 0, beam.width, beamHeight, [0, 1, 1, 0.8])
    this.renderer.drawQuad(x + beam.width/2, y, 1, beam.width, beamHeight/2, [1, 1, 1, 0.9])
  }

  private renderMissile(missile: ReturnType<Simulation['getState']>['missiles'][0]): void {
    const x = missile.x + this.shakeOffset.x
    const y = missile.y + this.shakeOffset.y
    const angle = Math.atan2(missile.vy, missile.vx)

    // Missile trail
    this.renderer.drawQuad(x - 15, y, -1, 20, 6, [1, 0.5, 0, 0.4], angle)
    // Missile body
    this.renderer.drawQuad(x, y, 0, 16, 6, [0.6, 0.6, 0.6, 1], angle)
    // Missile tip
    this.renderer.drawQuad(x + 6, y, 1, 6, 4, [1, 0.3, 0, 1], angle)
  }

  private renderPowerup(powerup: ReturnType<Simulation['getState']>['powerups'][0]): void {
    const x = powerup.x + this.shakeOffset.x
    const y = powerup.y + this.shakeOffset.y
    const bob = Math.sin(powerup.frame * 0.1) * 3
    const color = COLORS[powerup.type as keyof typeof COLORS] as [number, number, number, number] || COLORS.SHIELD

    // Special glow for life powerup
    if (powerup.type === 'LIFE') {
      const pulse = Math.sin(powerup.frame * 0.15) * 4
      this.renderer.drawQuad(x, y + bob, -1, 35 + pulse, 35 + pulse, [1, 0.3, 0.3, 0.3])
    }

    // Powerup glow
    this.renderer.drawQuad(x, y + bob, -0.5, 28, 28, [color[0], color[1], color[2], 0.3])
    // Powerup body
    this.renderer.drawQuad(x, y + bob, 0, 20, 16, color)
    // Powerup highlight
    this.renderer.drawQuad(x, y + bob, 1, 14, 10, [1, 1, 1, 0.8])
  }

  private renderParticle(particle: ReturnType<Simulation['getState']>['particles'][0]): void {
    const x = particle.x + this.shakeOffset.x
    const y = particle.y + this.shakeOffset.y
    const color = COLORS.explosion[particle.colorIndex % COLORS.explosion.length] ?? COLORS.explosion[0]!
    const size = Math.max(1, particle.size)

    this.renderer.drawQuad(x, y, -2, size, size, color)
  }

  // ==========================================================================
  // HUD Rendering
  // ==========================================================================

  private renderHUD(state: ReturnType<Simulation['getState']>): void {
    const localPlayer = state.players.find(p => p.playerId === this.localPlayerId)
    if (!localPlayer) return

    // Shield bar background
    this.renderer.drawQuad(-400, 250, 50, 154, 18, [0.1, 0.1, 0.15, 0.9])
    // Shield bar border
    this.renderer.drawQuad(-400, 250, 51, 152, 16, [0, 0.5, 0.5, 0.8])
    // Shield bar fill
    const shieldRatio = localPlayer.shields / localPlayer.maxShields
    const shieldColor: [number, number, number, number] = shieldRatio > 0.25
      ? [0, 1, 0.5, 1]
      : [1, 0.3, 0.2, 1]
    this.renderer.drawQuad(-400 - (1 - shieldRatio) * 75, 250, 52, 150 * shieldRatio, 12, shieldColor)

    // Lives display
    for (let i = 0; i < localPlayer.lives; i++) {
      this.renderer.drawQuad(-420 + i * 20, 225, 50, 12, 12, [1, 0.3, 0.3, 1])
    }

    // Ship level indicator
    for (let i = 0; i < localPlayer.shipLevel; i++) {
      this.renderer.drawQuad(-420 + i * 15, 200, 50, 10, 10, [1, 1, 0, 1])
    }

    // Powerup indicators
    let powerupX = -420
    const powerups = localPlayer.powerups
    const powerupColors: Array<[string, [number, number, number, number]]> = [
      ['spread', COLORS.SPREAD],
      ['laser', COLORS.LASER],
      ['missile', COLORS.MISSILE],
      ['rapid', COLORS.RAPID],
      ['pierce', COLORS.PIERCE],
      ['speed', COLORS.SPEED],
    ]

    for (const [key, color] of powerupColors) {
      const count = powerups[key as keyof typeof powerups]
      for (let i = 0; i < count; i++) {
        this.renderer.drawQuad(powerupX, 175, 50, 12, 12, color)
        powerupX += 14
      }
    }

    // Score display (top right)
    // Using quads to approximate score display position
    this.renderer.drawQuad(380, 250, 50, 100, 30, [0.1, 0.1, 0.15, 0.9])

    // Multiplier indicator
    const multiplierWidth = Math.min(100, state.multiplier * 12.5)
    this.renderer.drawQuad(380 - (100 - multiplierWidth)/2, 225, 50, multiplierWidth, 8, [1, 0, 1, 0.8])

    // Wave indicator
    this.renderer.drawQuad(380, 200, 50, 50, 20, [0.1, 0.1, 0.15, 0.9])
    // Wave progress bar
    const waveProgress = Math.min(1, state.enemies.length / 10)
    this.renderer.drawQuad(380 - (50 - 50 * waveProgress)/2, 200, 51, 50 * waveProgress, 16, [0, 0.5, 1, 0.6])

    // Boss warning
    if (state.bossActive && state.boss) {
      const pulse = Math.sin(Date.now() / 200) * 0.3 + 0.7
      this.renderer.drawQuad(0, 200, 60, 200, 40, [1, 0, 0, pulse * 0.3])
    }
  }

  // ==========================================================================
  // Public Accessors
  // ==========================================================================

  getState(): GameState {
    return this.state
  }

  getSimulation(): Simulation | null {
    return this.simulation
  }
}
