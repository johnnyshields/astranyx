import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import {
  AssetCache,
  AssetLoader,
  loadImage,
  loadAudio,
  createAssetLoader,
  assetCache,
} from './AssetLoader'

describe('AssetCache', () => {
  let cache: AssetCache

  beforeEach(() => {
    cache = new AssetCache()
  })

  describe('images', () => {
    it('should store and retrieve images', () => {
      const mockImage = document.createElement('img')
      cache.setImage('test.png', mockImage)
      expect(cache.getImage('test.png')).toBe(mockImage)
    })

    it('should return undefined for missing images', () => {
      expect(cache.getImage('nonexistent.png')).toBeUndefined()
    })
  })

  describe('audio', () => {
    it('should store and retrieve audio', () => {
      const mockAudio = document.createElement('audio')
      cache.setAudio('test.mp3', mockAudio)
      expect(cache.getAudio('test.mp3')).toBe(mockAudio)
    })

    it('should return undefined for missing audio', () => {
      expect(cache.getAudio('nonexistent.mp3')).toBeUndefined()
    })
  })

  describe('clear', () => {
    it('should clear all cached assets', () => {
      const mockImage = document.createElement('img')
      const mockAudio = document.createElement('audio')
      cache.setImage('test.png', mockImage)
      cache.setAudio('test.mp3', mockAudio)

      cache.clear()

      expect(cache.getImage('test.png')).toBeUndefined()
      expect(cache.getAudio('test.mp3')).toBeUndefined()
    })
  })
})

describe('loadImage', () => {
  it('should resolve with image element on successful load', async () => {
    let imageInstance: {
      onload: (() => void) | null
      onerror: (() => void) | null
      src: string
    } | null = null

    const MockImage = vi.fn().mockImplementation(function(this: HTMLImageElement) {
      imageInstance = {
        onload: null,
        onerror: null,
        src: '',
      }
      setTimeout(() => imageInstance?.onload?.(), 0)
      return imageInstance as unknown as HTMLImageElement
    })
    vi.stubGlobal('Image', MockImage)

    const result = await loadImage('test.png')
    expect(result).toBe(imageInstance)
    expect(imageInstance!.src).toBe('test.png')

    vi.unstubAllGlobals()
  })

  it('should reject on load error', async () => {
    let imageInstance: {
      onload: (() => void) | null
      onerror: (() => void) | null
      src: string
    } | null = null

    const MockImage = vi.fn().mockImplementation(function(this: HTMLImageElement) {
      imageInstance = {
        onload: null,
        onerror: null,
        src: '',
      }
      setTimeout(() => imageInstance?.onerror?.(), 0)
      return imageInstance as unknown as HTMLImageElement
    })
    vi.stubGlobal('Image', MockImage)

    await expect(loadImage('bad.png')).rejects.toThrow('Failed to load image: bad.png')

    vi.unstubAllGlobals()
  })
})

describe('loadAudio', () => {
  it('should resolve with audio element on successful load', async () => {
    let audioInstance: {
      oncanplaythrough: (() => void) | null
      onerror: (() => void) | null
      src: string
    } | null = null

    const MockAudio = vi.fn().mockImplementation(function(this: HTMLAudioElement) {
      audioInstance = {
        oncanplaythrough: null,
        onerror: null,
        src: '',
      }
      setTimeout(() => audioInstance?.oncanplaythrough?.(), 0)
      return audioInstance as unknown as HTMLAudioElement
    })
    vi.stubGlobal('Audio', MockAudio)

    const result = await loadAudio('test.mp3')
    expect(result).toBe(audioInstance)
    expect(audioInstance!.src).toBe('test.mp3')

    vi.unstubAllGlobals()
  })

  it('should reject on load error', async () => {
    let audioInstance: {
      oncanplaythrough: (() => void) | null
      onerror: (() => void) | null
      src: string
    } | null = null

    const MockAudio = vi.fn().mockImplementation(function(this: HTMLAudioElement) {
      audioInstance = {
        oncanplaythrough: null,
        onerror: null,
        src: '',
      }
      setTimeout(() => audioInstance?.onerror?.(), 0)
      return audioInstance as unknown as HTMLAudioElement
    })
    vi.stubGlobal('Audio', MockAudio)

    await expect(loadAudio('bad.mp3')).rejects.toThrow('Failed to load audio: bad.mp3')

    vi.unstubAllGlobals()
  })
})

describe('AssetLoader', () => {
  beforeEach(() => {
    assetCache.clear()
  })

  describe('constructor', () => {
    it('should create loader with manifest', () => {
      const loader = new AssetLoader({ images: ['a.png'], audio: ['b.mp3'] })
      expect(loader).toBeInstanceOf(AssetLoader)
    })
  })

  describe('progress', () => {
    it('should set progress callback and return this', () => {
      const loader = new AssetLoader({})
      const callback = vi.fn()
      const result = loader.progress(callback)
      expect(result).toBe(loader)
    })
  })

  describe('load', () => {
    it('should return cache immediately for empty manifest', async () => {
      const loader = new AssetLoader({})
      const result = await loader.load()
      expect(result).toBe(assetCache)
    })

    it('should return cache for manifest with empty arrays', async () => {
      const loader = new AssetLoader({ images: [], audio: [] })
      const result = await loader.load()
      expect(result).toBe(assetCache)
    })

    it('should call progress callback', async () => {
      const mockImage = {
        onload: null as (() => void) | null,
        onerror: null as (() => void) | null,
        src: '',
      }

      const MockImage = vi.fn().mockImplementation(function(this: HTMLImageElement) {
        setTimeout(() => mockImage.onload?.(), 0)
        return mockImage as unknown as HTMLImageElement
      })
      vi.stubGlobal('Image', MockImage)

      const progressCallback = vi.fn()
      const loader = new AssetLoader({ images: ['test.png'] })
      loader.progress(progressCallback)

      await loader.load()

      expect(progressCallback).toHaveBeenCalledWith({
        loaded: 1,
        total: 1,
        percent: 100,
        currentAsset: 'test.png',
      })

      vi.unstubAllGlobals()
    })

    it('should handle failed loads gracefully', async () => {
      const mockImage = {
        onload: null as (() => void) | null,
        onerror: null as (() => void) | null,
        src: '',
      }

      const MockImage = vi.fn().mockImplementation(function(this: HTMLImageElement) {
        setTimeout(() => mockImage.onerror?.(), 0)
        return mockImage as unknown as HTMLImageElement
      })
      vi.stubGlobal('Image', MockImage)

      const warnSpy = vi.spyOn(console, 'warn').mockImplementation(() => {})

      const loader = new AssetLoader({ images: ['bad.png'] })
      const result = await loader.load()

      expect(result).toBe(assetCache)
      expect(warnSpy).toHaveBeenCalled()

      vi.unstubAllGlobals()
      vi.restoreAllMocks()
    })
  })

  describe('loadParallel', () => {
    it('should return cache immediately for empty manifest', async () => {
      const loader = new AssetLoader({})
      const result = await loader.loadParallel()
      expect(result).toBe(assetCache)
    })

    it('should load with concurrency limit', async () => {
      const MockImage = vi.fn().mockImplementation(function(this: HTMLImageElement) {
        const instance = {
          onload: null as (() => void) | null,
          onerror: null as (() => void) | null,
          src: '',
        }
        queueMicrotask(() => instance.onload?.())
        return instance as unknown as HTMLImageElement
      })
      vi.stubGlobal('Image', MockImage)

      const progressCallback = vi.fn()
      const loader = new AssetLoader({ images: ['a.png', 'b.png'] })
      loader.progress(progressCallback)

      await loader.loadParallel(2)

      expect(progressCallback).toHaveBeenCalledTimes(2)

      vi.unstubAllGlobals()
    })
  })
})

describe('createAssetLoader', () => {
  it('should create AssetLoader instance', () => {
    const loader = createAssetLoader({ images: ['test.png'] })
    expect(loader).toBeInstanceOf(AssetLoader)
  })
})

describe('assetCache', () => {
  it('should be a global instance', () => {
    expect(assetCache).toBeInstanceOf(AssetCache)
  })
})
