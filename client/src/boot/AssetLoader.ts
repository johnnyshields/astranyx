/**
 * Asset loading utilities
 * Handles progressive loading of images, audio, and other assets
 */

import { SafeConsole } from '../core/SafeConsole.ts'

export interface AssetManifest {
  images?: string[]
  audio?: string[]
  fonts?: string[]
}

export interface LoadProgress {
  loaded: number
  total: number
  percent: number
  currentAsset: string
}

export type ProgressCallback = (progress: LoadProgress) => void

/**
 * Asset cache for loaded resources
 */
export class AssetCache {
  private images = new Map<string, HTMLImageElement>()
  private audio = new Map<string, HTMLAudioElement>()

  setImage(key: string, image: HTMLImageElement): void {
    this.images.set(key, image)
  }

  getImage(key: string): HTMLImageElement | undefined {
    return this.images.get(key)
  }

  setAudio(key: string, audio: HTMLAudioElement): void {
    this.audio.set(key, audio)
  }

  getAudio(key: string): HTMLAudioElement | undefined {
    return this.audio.get(key)
  }

  clear(): void {
    this.images.clear()
    this.audio.clear()
  }
}

/**
 * Global asset cache instance
 */
export const assetCache = new AssetCache()

/**
 * Load a single image
 */
export function loadImage(src: string): Promise<HTMLImageElement> {
  return new Promise((resolve, reject) => {
    const img = new Image()
    img.onload = () => resolve(img)
    img.onerror = () => reject(new Error(`Failed to load image: ${src}`))
    img.src = src
  })
}

/**
 * Load a single audio file
 */
export function loadAudio(src: string): Promise<HTMLAudioElement> {
  return new Promise((resolve, reject) => {
    const audio = new Audio()
    audio.oncanplaythrough = () => resolve(audio)
    audio.onerror = () => reject(new Error(`Failed to load audio: ${src}`))
    audio.src = src
  })
}

/**
 * Load multiple assets with progress reporting
 */
export class AssetLoader {
  private manifest: AssetManifest
  private onProgress: ProgressCallback | null = null

  constructor(manifest: AssetManifest) {
    this.manifest = manifest
  }

  /**
   * Set progress callback
   */
  progress(callback: ProgressCallback): this {
    this.onProgress = callback
    return this
  }

  /**
   * Load all assets
   */
  async load(): Promise<AssetCache> {
    const images = this.manifest.images ?? []
    const audio = this.manifest.audio ?? []
    const total = images.length + audio.length

    if (total === 0) {
      return assetCache
    }

    let loaded = 0

    const reportProgress = (asset: string) => {
      loaded++
      this.onProgress?.({
        loaded,
        total,
        percent: Math.round((loaded / total) * 100),
        currentAsset: asset,
      })
    }

    // Load images
    for (const src of images) {
      try {
        const img = await loadImage(src)
        assetCache.setImage(src, img)
        reportProgress(src)
      } catch (e) {
        SafeConsole.warn(`Failed to load image: ${src}`, e)
        reportProgress(src)
      }
    }

    // Load audio
    for (const src of audio) {
      try {
        const aud = await loadAudio(src)
        assetCache.setAudio(src, aud)
        reportProgress(src)
      } catch (e) {
        SafeConsole.warn(`Failed to load audio: ${src}`, e)
        reportProgress(src)
      }
    }

    return assetCache
  }

  /**
   * Load assets in parallel with concurrency limit
   */
  async loadParallel(concurrency: number = 4): Promise<AssetCache> {
    const images = this.manifest.images ?? []
    const audio = this.manifest.audio ?? []
    const total = images.length + audio.length

    if (total === 0) {
      return assetCache
    }

    let loaded = 0

    const reportProgress = (asset: string) => {
      loaded++
      this.onProgress?.({
        loaded,
        total,
        percent: Math.round((loaded / total) * 100),
        currentAsset: asset,
      })
    }

    // Create load tasks
    const tasks: Array<() => Promise<void>> = []

    for (const src of images) {
      tasks.push(async () => {
        try {
          const img = await loadImage(src)
          assetCache.setImage(src, img)
        } catch (e) {
          SafeConsole.warn(`Failed to load image: ${src}`, e)
        }
        reportProgress(src)
      })
    }

    for (const src of audio) {
      tasks.push(async () => {
        try {
          const aud = await loadAudio(src)
          assetCache.setAudio(src, aud)
        } catch (e) {
          SafeConsole.warn(`Failed to load audio: ${src}`, e)
        }
        reportProgress(src)
      })
    }

    // Run with concurrency limit
    await runWithConcurrency(tasks, concurrency)

    return assetCache
  }
}

/**
 * Run async tasks with concurrency limit
 */
async function runWithConcurrency(
  tasks: Array<() => Promise<void>>,
  limit: number
): Promise<void> {
  const executing: Promise<void>[] = []

  for (const task of tasks) {
    const p = task().then(() => {
      executing.splice(executing.indexOf(p), 1)
    })
    executing.push(p)

    if (executing.length >= limit) {
      await Promise.race(executing)
    }
  }

  await Promise.all(executing)
}

/**
 * Preload critical assets (call early in boot)
 */
export async function preloadCritical(): Promise<void> {
  // Preload fonts
  if (document.fonts) {
    await document.fonts.ready
  }
}

/**
 * Create asset loader with manifest
 */
export function createAssetLoader(manifest: AssetManifest): AssetLoader {
  return new AssetLoader(manifest)
}
