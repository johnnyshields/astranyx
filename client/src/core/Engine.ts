import { Renderer } from './Renderer.ts'
import { Input } from './Input.ts'
import type { Game } from '../game/Game.ts'

export type InitPhase = 'renderer' | 'input' | 'game' | 'ready'
export type InitCallback = (phase: InitPhase, progress: number) => void

export class Engine {
  private canvas: HTMLCanvasElement
  private renderer!: Renderer
  private input!: Input
  private game!: Game

  private lastTime = 0
  private running = false
  private frameId = 0

  // Fixed timestep for game logic (60 Hz)
  private readonly TICK_RATE = 1000 / 60
  private accumulator = 0

  private onInit: InitCallback | null = null

  constructor(canvas: HTMLCanvasElement) {
    this.canvas = canvas
  }

  /**
   * Set initialization progress callback
   */
  onProgress(callback: InitCallback): this {
    this.onInit = callback
    return this
  }

  async init(): Promise<void> {
    // Initialize WebGL2 renderer
    this.onInit?.('renderer', 0)
    this.renderer = new Renderer(this.canvas)
    await this.renderer.init()
    this.onInit?.('renderer', 25)

    // Initialize input handling
    this.onInit?.('input', 25)
    this.input = new Input()
    this.input.init()
    this.onInit?.('input', 40)

    // Lazy load and initialize game module
    this.onInit?.('game', 40)
    const { Game } = await import('../game/Game.ts')
    this.onInit?.('game', 70)

    this.game = new Game(this.renderer, this.input)
    await this.game.init()
    this.onInit?.('game', 90)

    // Handle resize
    this.resize()
    window.addEventListener('resize', () => this.resize())

    this.onInit?.('ready', 100)
  }

  private resize(): void {
    const dpr = window.devicePixelRatio || 1
    const width = window.innerWidth
    const height = window.innerHeight

    this.canvas.width = width * dpr
    this.canvas.height = height * dpr
    this.canvas.style.width = `${width}px`
    this.canvas.style.height = `${height}px`

    this.renderer.resize(this.canvas.width, this.canvas.height)
    this.game.resize(width, height)
  }

  start(): void {
    if (this.running) return
    this.running = true
    this.lastTime = performance.now()
    this.loop(this.lastTime)
  }

  stop(): void {
    this.running = false
    if (this.frameId) {
      cancelAnimationFrame(this.frameId)
    }
  }

  /**
   * Get the game instance for external wiring (e.g., multiplayer)
   */
  getGame(): Game {
    return this.game
  }

  private loop = (currentTime: number): void => {
    if (!this.running) return

    const deltaTime = currentTime - this.lastTime
    this.lastTime = currentTime

    // Accumulate time for fixed timestep updates
    this.accumulator += deltaTime

    // Cap accumulator to prevent spiral of death
    if (this.accumulator > 200) {
      this.accumulator = 200
    }

    // Fixed timestep game logic updates
    while (this.accumulator >= this.TICK_RATE) {
      this.game.update(this.TICK_RATE / 1000)
      this.accumulator -= this.TICK_RATE
    }

    // Render with interpolation factor
    const alpha = this.accumulator / this.TICK_RATE
    this.game.render(alpha)

    this.frameId = requestAnimationFrame(this.loop)
  }
}
