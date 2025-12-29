import { defineConfig } from 'vite'

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
  },
  build: {
    outDir: 'dist',
    sourcemap: true,
  },
})
