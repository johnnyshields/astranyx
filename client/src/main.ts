import { Engine } from './core/Engine.ts'

async function main() {
  const canvas = document.getElementById('game') as HTMLCanvasElement
  const loading = document.getElementById('loading') as HTMLElement

  if (!canvas) {
    throw new Error('Canvas element not found')
  }

  try {
    const engine = new Engine(canvas)
    await engine.init()

    loading.style.display = 'none'
    engine.start()

    console.log('ASTRANYX initialized')
  } catch (error) {
    loading.textContent = 'INITIALIZATION FAILED'
    loading.style.color = '#f00'
    console.error('Failed to initialize engine:', error)
  }
}

main()
