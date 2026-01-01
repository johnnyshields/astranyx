/**
 * Boot loader - minimal initial bundle
 * Handles loading screen and progressive module loading
 */

export interface LoadingState {
  phase: 'init' | 'assets' | 'engine' | 'ready' | 'error'
  progress: number  // 0-100
  message: string
}

export type LoadingCallback = (state: LoadingState) => void

/**
 * Boot class handles the initial loading sequence
 */
export class Boot {
  private loadingEl: HTMLElement | null
  private callback: LoadingCallback | null = null

  constructor() {
    this.loadingEl = document.getElementById('loading')
  }

  /**
   * Set callback for loading state updates
   */
  onProgress(callback: LoadingCallback): void {
    this.callback = callback
  }

  /**
   * Update loading state
   */
  private updateState(state: LoadingState): void {
    if (this.loadingEl) {
      this.loadingEl.textContent = state.message
    }
    this.callback?.(state)
  }

  /**
   * Run the boot sequence
   */
  async run(): Promise<{ Engine: typeof import('../core/Engine.ts').Engine }> {
    try {
      // Phase 1: Initialize
      this.updateState({
        phase: 'init',
        progress: 0,
        message: 'INITIALIZING...',
      })

      // Check graphics support (WebGPU preferred, WebGL2 fallback)
      const canvas = document.getElementById('game') as HTMLCanvasElement
      if (!canvas) {
        throw new Error('Canvas element not found')
      }

      const graphicsBackend = await this.checkGraphicsSupport(canvas)

      this.updateState({
        phase: 'init',
        progress: 10,
        message: `${graphicsBackend} OK...`,
      })

      // Phase 2: Load assets (fonts, etc.)
      this.updateState({
        phase: 'assets',
        progress: 20,
        message: 'LOADING ASSETS...',
      })

      await this.loadAssets()

      this.updateState({
        phase: 'assets',
        progress: 40,
        message: 'ASSETS LOADED...',
      })

      // Phase 3: Load engine module
      this.updateState({
        phase: 'engine',
        progress: 50,
        message: 'LOADING ENGINE...',
      })

      const engineModule = await import('../core/Engine.ts')

      this.updateState({
        phase: 'engine',
        progress: 80,
        message: 'ENGINE LOADED...',
      })

      // Phase 4: Ready
      this.updateState({
        phase: 'ready',
        progress: 100,
        message: 'READY',
      })

      return { Engine: engineModule.Engine }

    } catch (error) {
      const message = error instanceof Error ? error.message : 'Unknown error'
      this.updateState({
        phase: 'error',
        progress: 0,
        message: `ERROR: ${message}`,
      })
      throw error
    }
  }

  /**
   * Check graphics support (WebGPU preferred, WebGL2 fallback)
   */
  private async checkGraphicsSupport(canvas: HTMLCanvasElement): Promise<string> {
    // Check WebGPU first
    if ('gpu' in navigator) {
      try {
        const gpu = navigator.gpu as GPU
        const adapter = await gpu.requestAdapter()
        if (adapter) {
          return 'WEBGPU'
        }
      } catch {
        // WebGPU not available, fall through to WebGL2
      }
    }

    // Fall back to WebGL2
    const gl = canvas.getContext('webgl2')
    if (!gl) {
      throw new Error('Neither WebGPU nor WebGL2 supported')
    }

    return 'WEBGL2'
  }

  /**
   * Load required assets
   */
  private async loadAssets(): Promise<void> {
    // Wait for fonts to load
    if (document.fonts) {
      await document.fonts.ready
    }

    // Small delay to ensure DOM is ready
    await new Promise(resolve => setTimeout(resolve, 100))
  }

  /**
   * Hide loading screen
   */
  hideLoading(): void {
    if (this.loadingEl) {
      this.loadingEl.style.display = 'none'
    }
  }

  /**
   * Show error state
   */
  showError(message: string): void {
    if (this.loadingEl) {
      this.loadingEl.textContent = message
      this.loadingEl.style.color = '#f00'
      this.loadingEl.style.display = 'block'
    }
  }
}
