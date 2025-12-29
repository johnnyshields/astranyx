import { Renderer } from './Renderer.ts'
import { Input } from './Input.ts'
import { Game } from '../game/Game.ts'

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

  constructor(canvas: HTMLCanvasElement) {
    this.canvas = canvas
  }

  async init(): Promise<void> {
    // Initialize WebGL2 renderer
    this.renderer = new Renderer(this.canvas)
    await this.renderer.init()

    // Initialize input handling
    this.input = new Input()
    this.input.init()

    // Initialize game
    this.game = new Game(this.renderer, this.input)
    await this.game.init()

    // Handle resize
    this.resize()
    window.addEventListener('resize', () => this.resize())
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
