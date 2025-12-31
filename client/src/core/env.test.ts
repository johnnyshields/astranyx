import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest'
import {
  isDevBuild,
  isProdBuild,
  getEnvironment,
  isTest,
  isDevelopment,
  isPreview,
  isStaging,
  isProduction,
  isLocal,
  isRemote,
} from './env'

describe('env', () => {
  describe('isDevBuild', () => {
    it('returns boolean based on import.meta.env.DEV', () => {
      // In test environment, DEV is typically false
      expect(typeof isDevBuild()).toBe('boolean')
    })
  })

  describe('isProdBuild', () => {
    it('returns boolean based on import.meta.env.PROD', () => {
      expect(typeof isProdBuild()).toBe('boolean')
    })
  })

  describe('getEnvironment', () => {
    it('returns test in vitest environment', () => {
      // Vitest sets VITEST=true
      expect(getEnvironment()).toBe('test')
    })

    it('returns a valid environment string', () => {
      const env = getEnvironment()
      expect(['development', 'test', 'preview', 'staging', 'production']).toContain(env)
    })
  })

  describe('environment checks', () => {
    it('isTest returns true in test environment', () => {
      expect(isTest()).toBe(true)
    })

    it('isDevelopment returns false in test environment', () => {
      expect(isDevelopment()).toBe(false)
    })

    it('isPreview returns false in test environment', () => {
      expect(isPreview()).toBe(false)
    })

    it('isStaging returns false in test environment', () => {
      expect(isStaging()).toBe(false)
    })

    it('isProduction returns false in test environment', () => {
      expect(isProduction()).toBe(false)
    })
  })

  describe('composite checks', () => {
    it('isLocal returns true in test environment', () => {
      // test is considered local
      expect(isLocal()).toBe(true)
    })

    it('isRemote returns false in test environment', () => {
      expect(isRemote()).toBe(false)
    })

    it('isLocal and isRemote are mutually exclusive', () => {
      expect(isLocal()).not.toBe(isRemote())
    })
  })
})
