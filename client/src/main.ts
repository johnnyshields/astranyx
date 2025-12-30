/**
 * ASTRANYX - Main Entry Point
 *
 * This is the minimal boot loader that handles:
 * 1. Initial loading screen
 * 2. Progressive module loading
 * 3. Error handling
 *
 * Heavy modules (Game, Simulation, Renderer) are lazy-loaded
 * to minimize initial bundle size and improve load times.
 */

import { Boot } from './boot/Boot.ts'

async function main() {
  const boot = new Boot()

  // Optional: Add progress listener for custom UI
  boot.onProgress((state) => {
    console.log(`[Boot] ${state.phase}: ${state.progress}% - ${state.message}`)
  })

  try {
    // Run boot sequence (loads Engine module)
    const { Engine } = await boot.run()

    // Get canvas element
    const canvas = document.getElementById('game') as HTMLCanvasElement
    if (!canvas) {
      throw new Error('Canvas element not found')
    }

    // Create engine instance
    const engine = new Engine(canvas)

    // Optional: Track engine init progress
    engine.onProgress((phase, progress) => {
      const messages: Record<string, string> = {
        renderer: 'INITIALIZING RENDERER...',
        input: 'CONFIGURING INPUT...',
        game: 'LOADING GAME...',
        ready: 'READY',
      }
      const loading = document.getElementById('loading')
      if (loading) {
        loading.textContent = messages[phase] ?? 'LOADING...'
      }
    })

    // Initialize engine (lazy loads Game module)
    await engine.init()

    // Hide loading screen and start
    boot.hideLoading()
    engine.start()

    console.log('ASTRANYX initialized')

  } catch (error) {
    const message = error instanceof Error ? error.message : 'Unknown error'
    boot.showError(`INITIALIZATION FAILED: ${message}`)
    console.error('Failed to initialize:', error)
  }
}

// Start the application
main()
