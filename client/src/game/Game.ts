import type { Renderer, MeshHandle } from '../core/Renderer.ts'
import type { Input } from '../core/Input.ts'
import { Simulation, type EnemyType, type BulletType, type PowerupType, type BossType } from './Simulation.ts'
import { LockstepNetcode, type PlayerInput } from '../network/LockstepNetcode.ts'

// Mesh file paths
const MESH_PATHS = {
  playerShip: '/assets/meshes/player-ship.glb',
  enemyShip: '/assets/meshes/enemy-ship.glb',
  tank: '/assets/meshes/tank.glb',
  bossCore: '/assets/meshes/boss-core.glb',
  drone: '/assets/meshes/drone.glb',
  orb: '/assets/meshes/orb.glb',
  powerup: '/assets/meshes/powerup.glb',
  mine: '/assets/meshes/mine.glb',
}

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

// Enemy render config (scale and depth by type)
const ENEMY_RENDER_CONFIG: Record<string, { scale: number; depth: number }> = {
  grunt: { scale: 35, depth: 0.6 },
  shooter: { scale: 40, depth: 0.6 },
  swerver: { scale: 32, depth: 0.6 },
  tank: { scale: 65, depth: 0.8 },
  speeder: { scale: 38, depth: 0.4 },
  bomber: { scale: 50, depth: 0.7 },
  sniper: { scale: 45, depth: 0.6 },
  carrier: { scale: 80, depth: 0.8 },
  mine: { scale: 30, depth: 1.0 },
  spiral: { scale: 50, depth: 0.6 },
  shield: { scale: 55, depth: 0.6 },
  splitter: { scale: 45, depth: 0.6 },
}

// Boss sizes by type (w=width, h=height, d=depth)
const BOSS_SIZES = [
  { w: 100, h: 90, d: 70 },   // CLASSIC
  { w: 80, h: 60, d: 50 },    // TWIN
  { w: 120, h: 100, d: 80 },  // CARRIER
  { w: 100, h: 70, d: 60 },   // LASER
  { w: 70, h: 180, d: 50 },   // WALL
  { w: 130, h: 120, d: 100 }, // FINAL
]

// Get health bar color based on health ratio
function getHealthBarColor(healthRatio: number): [number, number, number, number] {
  if (healthRatio > 0.5) return [0, 0.8, 0.5, 1]
  if (healthRatio > 0.25) return [1, 1, 0, 1]
  return [1, 0.3, 0.2, 1]
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

  // 3D Meshes
  private meshes: {
    playerShip: MeshHandle | null
    enemyShip: MeshHandle | null
    tank: MeshHandle | null
    bossCore: MeshHandle | null
    drone: MeshHandle | null
    orb: MeshHandle | null
    powerup: MeshHandle | null
    mine: MeshHandle | null
  } = {
    playerShip: null,
    enemyShip: null,
    tank: null,
    bossCore: null,
    drone: null,
    orb: null,
    powerup: null,
    mine: null,
  }

  constructor(renderer: Renderer, input: Input) {
    this.renderer = renderer
    this.input = input
  }

  async init(): Promise<void> {
    // Load 3D meshes from GLB files
    const [playerShip, enemyShip, tank, bossCore, drone, orb, powerup, mine] = await Promise.all([
      this.renderer.loadGLB('playerShip', MESH_PATHS.playerShip),
      this.renderer.loadGLB('enemyShip', MESH_PATHS.enemyShip),
      this.renderer.loadGLB('tank', MESH_PATHS.tank),
      this.renderer.loadGLB('bossCore', MESH_PATHS.bossCore),
      this.renderer.loadGLB('drone', MESH_PATHS.drone),
      this.renderer.loadGLB('orb', MESH_PATHS.orb),
      this.renderer.loadGLB('powerup', MESH_PATHS.powerup),
      this.renderer.loadGLB('mine', MESH_PATHS.mine),
    ])

    this.meshes.playerShip = playerShip
    this.meshes.enemyShip = enemyShip
    this.meshes.tank = tank
    this.meshes.bossCore = bossCore
    this.meshes.drone = drone
    this.meshes.orb = orb
    this.meshes.powerup = powerup
    this.meshes.mine = mine

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

    console.log('Game initialized with 3D meshes')
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

    // Update play bounds from renderer (camera-compensated)
    if (this.simulation) {
      this.simulation.setPlayBounds(this.renderer.getPlayBounds())
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

      // Enemies (3D meshes only)
      for (const enemy of state.enemies) {
        this.renderEnemy(enemy)
      }

      // Boss (3D mesh only)
      if (state.boss) {
        this.renderBoss(state.boss)
      }

      // Players
      for (const player of state.players) {
        this.renderPlayer(player)
      }

      // Switch to HUD mode for flat UI elements
      this.renderer.beginHUD()

      // Enemy health bars (flat, screen-aligned)
      for (const enemy of state.enemies) {
        this.renderEnemyHealthBar(enemy)
      }

      // Boss health bar (flat, screen-aligned)
      if (state.boss) {
        this.renderBossHealthBar(state.boss)
      }

      // Draw main HUD
      this.renderHUD(state)

      this.renderer.endHUD()
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

    // Draw orbs using 3D mesh
    if (this.meshes.orb) {
      for (const orb of player.orbs) {
        const ox = x + Math.cos(orb.angle) * orb.radius
        const oy = y + Math.sin(orb.angle) * orb.radius
        const orbRotation = Date.now() / 500 + orb.angle

        // Orb glow (quad)
        this.renderer.drawQuad(ox, oy, -5, 22, 22, [1, 0, 1, 0.25])
        // Orb mesh
        this.renderer.drawMesh(
          this.meshes.orb,
          ox, oy, 0,
          25, 25, 25,
          [1, 0, 1, 1],
          orbRotation, orbRotation * 0.7, 0
        )
      }
    }

    // Draw drones using 3D mesh
    if (this.meshes.drone) {
      for (const drone of player.drones) {
        const droneRotation = Math.sin(Date.now() / 300 + drone.x) * 0.2
        this.renderer.drawMesh(
          this.meshes.drone,
          drone.x, drone.y, 0,
          20, 20, 20,
          [0.5, 1, 0.5, 1],
          0, droneRotation, 0
        )
      }
    }

    const color = isLocal ? COLORS.player1 : COLORS.player2
    const pitchRotation = -player.vy * 0.002  // Pitch up/down based on vertical movement
    const clampedPitch = Math.max(-0.4, Math.min(0.4, pitchRotation))
    const rollRotation = player.vx * 0.0008   // Subtle roll based on horizontal movement
    const clampedRoll = Math.max(-0.15, Math.min(0.15, rollRotation))

    // Ship size scales with level
    const baseScale = 50 + lvl * 12

    // Engine exhaust (animated quads - keep as 2D effects)
    const exhaustLength = 30 + Math.sin(player.chargeTime * 20) * 5
    this.renderer.drawQuad(x - baseScale/2 - exhaustLength/2, y, -5, exhaustLength, 10, [0.2, 0.5, 1.0, 0.5], clampedPitch)
    this.renderer.drawQuad(x - baseScale/2 - exhaustLength/3, y, -3, exhaustLength/2, 6, [0.5, 0.8, 1.0, 0.8], clampedPitch)

    // Draw 3D player ship mesh
    if (this.meshes.playerShip) {
      this.renderer.drawMesh(
        this.meshes.playerShip,
        x, y, 0,
        baseScale, baseScale, baseScale * 0.6,
        [0.6, 0.7, 0.8, 1.0],
        clampedPitch, clampedRoll, 0  // Pitch on X (up/down), subtle roll on Y (left/right)
      )

      // Cockpit glow overlay (quad)
      this.renderer.drawQuad(x + baseScale/4, y, 10, baseScale/5, baseScale/6, color, clampedPitch)
    }

    // Charge indicator
    if (player.charging) {
      const chargeSize = Math.min(player.chargeTime * 30, 24)
      this.renderer.drawQuad(x + baseScale/2 + 10, y, 15, chargeSize, chargeSize, [...color.slice(0, 3), 0.5 + Math.sin(Date.now() / 50) * 0.3] as [number, number, number, number])
    }

    // Invincibility shield (quad effect)
    if (player.invincible > 0 && player.invincible < 30) {
      this.renderer.drawQuad(x, y, -10, baseScale + 20, baseScale * 0.6 + 20, [...color.slice(0, 3), player.invincible / 60] as [number, number, number, number])
    }
  }

  private renderEnemy(enemy: ReturnType<Simulation['getState']>['enemies'][0]): void {
    const x = enemy.x + this.shakeOffset.x
    const y = enemy.y + this.shakeOffset.y
    const color = COLORS[enemy.type as keyof typeof COLORS] as [number, number, number, number] || COLORS.grunt

    // Size from config
    const config = ENEMY_RENDER_CONFIG[enemy.type] ?? { scale: 40, depth: 0.6 }
    const { scale, depth } = config

    // Shield effect
    if (enemy.hasShield) {
      this.renderer.drawQuad(x, y, -10, scale + 20, scale * depth + 20, [0, 0.8, 0.2, 0.3])
    }

    // Enemy glow (quad)
    this.renderer.drawQuad(x, y, -5, scale + 15, scale * depth + 15, [color[0], color[1], color[2], 0.2])

    // Select mesh based on enemy type
    const wobble = Math.sin(Date.now() / 400 + enemy.x * 0.01) * 0.15
    let mesh = this.meshes.enemyShip

    if (enemy.type === 'tank') {
      mesh = this.meshes.tank
    } else if (enemy.type === 'mine') {
      mesh = this.meshes.mine
      // Mines spin
      const spin = Date.now() / 500
      if (mesh) {
        this.renderer.drawMesh(
          mesh,
          x, y, 0,
          scale, scale, scale,
          color,
          spin, spin * 0.7, spin * 0.3
        )
      }
    }

    // Draw enemy mesh (unless it's a mine which was handled above)
    if (mesh && enemy.type !== 'mine') {
      this.renderer.drawMesh(
        mesh,
        x, y, 0,
        scale, scale * 0.8, scale * depth,
        color,
        0, wobble, 0
      )
    }
  }

  private renderEnemyHealthBar(enemy: ReturnType<Simulation['getState']>['enemies'][0]): void {
    // Get enemy scale from config
    const config = ENEMY_RENDER_CONFIG[enemy.type] ?? { scale: 40, depth: 0.6 }
    const { scale, depth } = config

    // Project world position to screen
    const worldX = enemy.x + this.shakeOffset.x
    const worldY = enemy.y + this.shakeOffset.y - scale * depth / 2 - 12
    const screen = this.renderer.worldToScreen(worldX, worldY, 0)

    // Health bar (flat, fixed size regardless of perspective)
    const healthRatio = enemy.health / enemy.maxHealth
    const barWidth = 40
    const barHeight = 4

    this.renderer.drawQuad(screen.x, screen.y, 0, barWidth + 2, barHeight + 2, [0.2, 0.2, 0.2, 0.8])
    this.renderer.drawQuad(screen.x - (1 - healthRatio) * barWidth / 2, screen.y, 0, barWidth * healthRatio, barHeight, getHealthBarColor(healthRatio))
  }

  private renderBoss(boss: ReturnType<Simulation['getState']>['boss']): void {
    if (!boss) return

    const x = boss.x + this.shakeOffset.x
    const y = boss.y + this.shakeOffset.y
    const color = COLORS.boss[boss.type] ?? COLORS.boss[0]!
    const size = BOSS_SIZES[boss.type] ?? BOSS_SIZES[0]!

    // Boss glow
    const pulse = Math.sin(Date.now() / 200) * 8
    const pulseSlow = Math.sin(Date.now() / 600) * 0.1
    this.renderer.drawQuad(x, y, -15, size.w + 40 + pulse, size.h + 40 + pulse, [color[0], color[1], color[2], 0.15])

    // Draw main boss body as 3D mesh
    if (this.meshes.bossCore) {
      this.renderer.drawMesh(
        this.meshes.bossCore,
        x, y, 0,
        size.w, size.h, size.d,
        color,
        pulseSlow, pulseSlow * 0.5, 0
      )
    }

    // Type-specific rendering
    switch (boss.type) {
      case 0: // CLASSIC - Core
        {
          const coreColor: [number, number, number, number] = boss.health / boss.maxHealth > 0.5
            ? [1, 1, 0, 1]
            : boss.health / boss.maxHealth > 0.25
              ? [1, 0.5, 0, 1]
              : [1, 0, 0, 1]
          // Pulsing core
          if (this.meshes.bossCore) {
            this.renderer.drawMesh(
              this.meshes.bossCore,
              x, y, 20,
              35 + pulse, 35 + pulse, 35 + pulse,
              coreColor,
              Date.now() / 1000, Date.now() / 800, 0
            )
          }
        }
        break

      case 1: // TWIN
        // Second body
        if (boss.twin && this.meshes.bossCore) {
          this.renderer.drawMesh(
            this.meshes.bossCore,
            x, boss.twin.y + this.shakeOffset.y, 0,
            60, 50, 40,
            color,
            pulseSlow, -pulseSlow * 0.5, 0
          )
          this.renderer.drawMesh(
            this.meshes.bossCore,
            x, boss.twin.y + this.shakeOffset.y, 15,
            25, 25, 25,
            [0, 1, 0, 1],
            Date.now() / 700, 0, 0
          )
        }
        // Main core
        if (this.meshes.bossCore) {
          this.renderer.drawMesh(
            this.meshes.bossCore,
            x, y, 15,
            25, 25, 25,
            [0, 1, 0, 1],
            Date.now() / 700, 0, 0
          )
        }
        break

      case 2: // CARRIER
        // Hangar bay (quad for glowing effect)
        this.renderer.drawQuad(x + 25, y, 15, 25, size.h * 0.5, [1, 1, 0, 0.8])
        break

      case 3: // LASER
        // Laser barrel
        this.renderer.drawQuad(x - size.w/2 - 40, y, 10, 60, 20, [0.5, 0.5, 0.5, 1])
        if (boss.charging) {
          const chargeSize = (boss.chargeTime || 0) * 15
          // Charging orb
          if (this.meshes.orb) {
            this.renderer.drawMesh(
              this.meshes.orb,
              x - size.w/2 - 60, y, 15,
              chargeSize, chargeSize, chargeSize,
              [1, 0, 0, 0.7 + Math.sin(Date.now() / 50) * 0.3],
              Date.now() / 200, Date.now() / 150, 0
            )
          }
        }
        break

      case 4: // WALL
        // Segments
        if (boss.segments && this.meshes.tank) {
          for (const seg of boss.segments) {
            const segColor: [number, number, number, number] = seg.hp > 0 ? [0.5, 0.5, 0.6, 1] : [0.2, 0.2, 0.2, 1]
            this.renderer.drawMesh(
              this.meshes.tank,
              x - 20, y + seg.y, 0,
              45, 35, 30,
              segColor,
              0, 0, 0
            )
            if (seg.hp > 0) {
              this.renderer.drawQuad(x - 35, y + seg.y, 15, 12, 10, [1, 0.3, 0.3, 1])
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
        if (this.meshes.bossCore) {
          this.renderer.drawMesh(
            this.meshes.bossCore,
            x, y, 20,
            50 + pulse, 50 + pulse, 50 + pulse,
            finalCoreColor,
            Date.now() / 400, Date.now() / 350, Date.now() / 500
          )
          // Inner core
          this.renderer.drawMesh(
            this.meshes.bossCore,
            x, y, 30,
            20, 20, 20,
            [1, 1, 1, 1],
            -Date.now() / 300, 0, 0
          )
        }
        // Cannons
        this.renderer.drawQuad(x - size.w/2 - 15, y - 20, 10, 30, 14, [1, 0.3, 0.3, 1])
        this.renderer.drawQuad(x - size.w/2 - 15, y + 20, 10, 30, 14, [1, 0.3, 0.3, 1])
        break
    }
  }

  private renderBossHealthBar(boss: ReturnType<Simulation['getState']>['boss']): void {
    if (!boss) return

    const size = BOSS_SIZES[boss.type] ?? BOSS_SIZES[0]!

    // Project world position to screen
    const worldX = boss.x + this.shakeOffset.x
    const worldY = boss.y + this.shakeOffset.y - size.h / 2 - 20
    const screen = this.renderer.worldToScreen(worldX, worldY, 0)

    // Health bar (flat, fixed size)
    const healthRatio = boss.health / boss.maxHealth
    const barWidth = 100
    const barHeight = 10

    this.renderer.drawQuad(screen.x, screen.y, 0, barWidth + 4, barHeight + 4, [0.2, 0.2, 0.2, 0.8])
    this.renderer.drawQuad(screen.x - (1 - healthRatio) * barWidth / 2, screen.y, 0, barWidth * healthRatio, barHeight, getHealthBarColor(healthRatio))
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
    const bob = Math.sin(powerup.frame * 0.1) * 5
    const color = COLORS[powerup.type as keyof typeof COLORS] as [number, number, number, number] || COLORS.SHIELD
    const spin = powerup.frame * 0.08

    // Special glow for life powerup
    if (powerup.type === 'LIFE') {
      const pulse = Math.sin(powerup.frame * 0.15) * 6
      this.renderer.drawQuad(x, y + bob, -10, 40 + pulse, 40 + pulse, [1, 0.3, 0.3, 0.3])
    }

    // Powerup glow (quad)
    this.renderer.drawQuad(x, y + bob, -5, 35, 35, [color[0], color[1], color[2], 0.3])

    // Draw 3D powerup mesh (spinning diamond)
    if (this.meshes.powerup) {
      this.renderer.drawMesh(
        this.meshes.powerup,
        x, y + bob, 0,
        30, 30, 30,
        color,
        spin, spin * 1.3, 0
      )
    }
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
