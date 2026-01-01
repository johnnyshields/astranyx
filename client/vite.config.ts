import { defineConfig } from 'vite'
import { readFileSync, existsSync } from 'fs'

// Detect WSL by checking /proc/version for Microsoft/WSL
const isWSL = existsSync('/proc/version') &&
  readFileSync('/proc/version', 'utf-8').toLowerCase().includes('microsoft')

export default defineConfig({
  root: '.',
  publicDir: 'public',
  server: {
    port: 4100,
    host: true,
    proxy: {
      '/socket': {
        target: 'ws://localhost:4200',
        ws: true,
      },
      '/api': {
        target: 'http://localhost:4200',
      },
    },
    // WSL2: use polling since inotify doesn't work across Windows/Linux boundary
    watch: isWSL ? {
      usePolling: true,
      interval: 300,
    } : undefined,
  },
  build: {
    outDir: 'dist',
    sourcemap: true,
  },
})
