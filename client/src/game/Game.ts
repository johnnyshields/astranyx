import type { Renderer } from '../core/Renderer.ts'
import type { Input } from '../core/Input.ts'
import { Simulation } from './Simulation.ts'
import { LockstepNetcode, emptyInput, type PlayerInput } from '../network/LockstepNetcode.ts'

export type GameState = 'title' | 'lobby' | 'connecting' | 'playing' | 'paused' | 'gameover'

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
    playerOrder: Map<string, number>,
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

    this.input.clearFrameState()
  }

  render(alpha: number): void {
    this.renderer.beginFrame(1 / 60)

    // Draw starfield
    for (const star of this.stars) {
      const brightness = (star.z + 600) / 500
      const size = 1 + brightness * 2
      this.renderer.drawQuad(
        star.x, star.y, star.z,
        size, size,
        [brightness * 0.8, brightness * 0.9, brightness, 1]
      )
    }

    // Draw game entities
    const state = this.currentState
    if (state) {
      for (const entity of state.entities) {
        this.renderEntity(entity, alpha)
      }

      // Draw HUD
      this.renderHUD(state)
    }

    // Draw pause overlay
    if (this.state === 'paused') {
      this.renderer.drawQuad(0, 0, 100, 2000, 1200, [0, 0, 0.1, 0.8])
    }

    // Show waiting indicator in multiplayer
    if (!this.singlePlayerMode && this.netcode?.isWaitingForInputs()) {
      this.renderer.drawQuad(0, 200, 100, 200, 30, [1, 0.5, 0, 0.8])
    }

    this.renderer.endFrame()
  }

  private renderEntity(
    entity: { type: string; x: number; y: number; rotation: number; health: number; playerId?: string },
    _alpha: number
  ): void {
    const { x, y, rotation } = entity

    switch (entity.type) {
      case 'player':
        this.renderPlayer(x, y, rotation, entity.playerId === this.localPlayerId)
        break
      case 'enemy':
        this.renderEnemy(x, y, rotation)
        break
      case 'bullet':
        this.renderBullet(x, y)
        break
    }
  }

  private renderPlayer(x: number, y: number, rotation: number, isLocal: boolean): void {
    const color: [number, number, number, number] = isLocal
      ? [0.0, 0.8, 1.0, 1.0]  // Cyan for local
      : [1.0, 0.5, 0.0, 1.0]  // Orange for remote

    // Engine exhaust
    this.renderer.drawQuad(x - 35, y, -1, 30, 10, [0.2, 0.5, 1.0, 0.5], rotation)
    this.renderer.drawQuad(x - 25, y, -0.5, 15, 6, [0.5, 0.8, 1.0, 0.8], rotation)

    // Main body
    this.renderer.drawQuad(x, y, 0, 60, 20, [0.6, 0.65, 0.75, 1.0], rotation)

    // Cockpit
    this.renderer.drawQuad(x + 15, y, 1, 20, 10, color, rotation)

    // Wings
    this.renderer.drawQuad(x - 5, y + 18, 0, 35, 8, [0.5, 0.55, 0.65, 1.0], rotation * 1.2)
    this.renderer.drawQuad(x - 5, y - 18, 0, 35, 8, [0.5, 0.55, 0.65, 1.0], rotation * 1.2)

    // Wing tips
    this.renderer.drawQuad(x - 20, y + 20, 0.5, 12, 4, [1.0, 0.3, 0.2, 1.0], rotation)
    this.renderer.drawQuad(x - 20, y - 20, 0.5, 12, 4, [1.0, 0.3, 0.2, 1.0], rotation)
  }

  private renderEnemy(x: number, y: number, rotation: number): void {
    // Enemy ship (facing left)
    this.renderer.drawQuad(x, y, 0, 40, 25, [0.8, 0.2, 0.2, 1.0], rotation)
    this.renderer.drawQuad(x - 10, y, 0.5, 20, 15, [1.0, 0.3, 0.3, 1.0], rotation)

    // Glow
    this.renderer.drawQuad(x, y, -1, 50, 35, [1.0, 0.2, 0.0, 0.2], rotation)
  }

  private renderBullet(x: number, y: number): void {
    // Bullet
    this.renderer.drawQuad(x, y, 0, 15, 4, [0.0, 1.0, 1.0, 1.0])
    // Glow
    this.renderer.drawQuad(x, y, -0.5, 20, 8, [0.0, 0.8, 1.0, 0.3])
  }

  private renderHUD(state: ReturnType<Simulation['getState']>): void {
    // Score display (just placeholder positioning)
    const localPlayer = state.entities.find(
      (e) => e.type === 'player' && e.playerId === this.localPlayerId
    )

    if (localPlayer) {
      // Health bar background
      this.renderer.drawQuad(-400, 250, 50, 104, 14, [0.2, 0.2, 0.2, 0.8])
      // Health bar fill
      const healthWidth = (localPlayer.health / 100) * 100
      const healthColor: [number, number, number, number] =
        localPlayer.health > 50 ? [0.0, 0.8, 0.5, 1.0] : [1.0, 0.3, 0.2, 1.0]
      this.renderer.drawQuad(-400 - (100 - healthWidth) / 2, 250, 51, healthWidth, 10, healthColor)
    }

    // Frame counter (debug)
    // Would need text rendering for proper display
  }

  getState(): GameState {
    return this.state
  }

  getSimulation(): Simulation | null {
    return this.simulation
  }
}
