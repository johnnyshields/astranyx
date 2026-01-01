import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { SafeConsole, log, warn, error, info, debug, group, groupEnd } from './SafeConsole'

describe('SafeConsole', () => {
  beforeEach(() => {
    vi.spyOn(console, 'log').mockImplementation(() => {})
    vi.spyOn(console, 'warn').mockImplementation(() => {})
    vi.spyOn(console, 'error').mockImplementation(() => {})
    vi.spyOn(console, 'info').mockImplementation(() => {})
    vi.spyOn(console, 'debug').mockImplementation(() => {})
    vi.spyOn(console, 'group').mockImplementation(() => {})
    vi.spyOn(console, 'groupEnd').mockImplementation(() => {})
  })

  afterEach(() => {
    vi.restoreAllMocks()
  })

  describe('exports', () => {
    it('exports individual functions', () => {
      expect(typeof log).toBe('function')
      expect(typeof warn).toBe('function')
      expect(typeof error).toBe('function')
      expect(typeof info).toBe('function')
      expect(typeof debug).toBe('function')
      expect(typeof group).toBe('function')
      expect(typeof groupEnd).toBe('function')
    })

    it('exports SafeConsole object with all methods', () => {
      expect(typeof SafeConsole.log).toBe('function')
      expect(typeof SafeConsole.warn).toBe('function')
      expect(typeof SafeConsole.error).toBe('function')
      expect(typeof SafeConsole.info).toBe('function')
      expect(typeof SafeConsole.debug).toBe('function')
      expect(typeof SafeConsole.group).toBe('function')
      expect(typeof SafeConsole.groupEnd).toBe('function')
    })
  })

  describe('error (always logs)', () => {
    it('calls console.error regardless of environment', () => {
      SafeConsole.error('test error')
      expect(console.error).toHaveBeenCalledWith('test error')
    })

    it('passes multiple arguments', () => {
      SafeConsole.error('error', { data: 123 }, 'more')
      expect(console.error).toHaveBeenCalledWith('error', { data: 123 }, 'more')
    })
  })

  // Note: In test environment, isDevBuild() returns false (PROD build)
  // so dev-only methods won't call console.*
  // We test that they don't throw and accept arguments correctly

  describe('log (dev only)', () => {
    it('accepts arguments without throwing', () => {
      expect(() => SafeConsole.log('test')).not.toThrow()
      expect(() => SafeConsole.log('a', 'b', 'c')).not.toThrow()
      expect(() => SafeConsole.log({ obj: true })).not.toThrow()
    })
  })

  describe('warn (dev only)', () => {
    it('accepts arguments without throwing', () => {
      expect(() => SafeConsole.warn('test')).not.toThrow()
      expect(() => SafeConsole.warn('a', 'b', 'c')).not.toThrow()
    })
  })

  describe('info (dev only)', () => {
    it('accepts arguments without throwing', () => {
      expect(() => SafeConsole.info('test')).not.toThrow()
      expect(() => SafeConsole.info('a', 'b', 'c')).not.toThrow()
    })
  })

  describe('debug (dev only)', () => {
    it('accepts arguments without throwing', () => {
      expect(() => SafeConsole.debug('test')).not.toThrow()
      expect(() => SafeConsole.debug('a', 'b', 'c')).not.toThrow()
    })
  })

  describe('group/groupEnd (dev only)', () => {
    it('accepts label without throwing', () => {
      expect(() => SafeConsole.group('test group')).not.toThrow()
      expect(() => SafeConsole.groupEnd()).not.toThrow()
    })
  })

  describe('function references', () => {
    it('individual exports match SafeConsole methods', () => {
      expect(log).toBe(SafeConsole.log)
      expect(warn).toBe(SafeConsole.warn)
      expect(error).toBe(SafeConsole.error)
      expect(info).toBe(SafeConsole.info)
      expect(debug).toBe(SafeConsole.debug)
      expect(group).toBe(SafeConsole.group)
      expect(groupEnd).toBe(SafeConsole.groupEnd)
    })
  })
})
