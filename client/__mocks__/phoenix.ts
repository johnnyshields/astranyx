/**
 * Mock for phoenix package - used during testing
 */
import { vi } from 'vitest'

// Create mock channel that can be customized per test
const createMockChannel = () => {
  const channel = {
    on: vi.fn().mockReturnThis(),
    join: vi.fn().mockReturnValue({
      receive: vi.fn().mockImplementation(function(this: { receive: (event: string, cb: (resp: unknown) => void) => unknown }, event: string, cb: (resp: unknown) => void) {
        if (event === 'ok') {
          // Use queueMicrotask for immediate async execution that works with fake timers
          queueMicrotask(() => cb({}))
        }
        return this
      }),
    }),
    push: vi.fn().mockReturnValue({
      receive: vi.fn().mockImplementation(function(this: { receive: (event: string, cb: (resp: unknown) => void) => unknown }, event: string, cb: (resp: unknown) => void) {
        if (event === 'ok') {
          queueMicrotask(() => cb({ latency: 10 }))
        }
        return this
      }),
    }),
    leave: vi.fn(),
  }
  return channel
}

// Mock Socket class that works as a constructor
export class Socket {
  private url: string
  private params: unknown
  private _openCallback: (() => void) | null = null
  private _errorCallback: ((err: unknown) => void) | null = null
  private _closeCallback: (() => void) | null = null
  private _connected = false

  constructor(url: string, params?: unknown) {
    this.url = url
    this.params = params
  }

  channel = vi.fn().mockImplementation(() => createMockChannel())

  connect() {
    this._connected = true
    // Use queueMicrotask for immediate async execution that works with fake timers
    queueMicrotask(() => this._openCallback?.())
  }

  disconnect() {
    this._connected = false
    queueMicrotask(() => this._closeCallback?.())
  }

  onOpen(callback: () => void) {
    this._openCallback = callback
  }

  onError(callback: (err: unknown) => void) {
    this._errorCallback = callback
  }

  onClose(callback: () => void) {
    this._closeCallback = callback
  }

  isConnected() {
    return this._connected
  }

  // Test helper to trigger error
  _triggerError(error: unknown) {
    this._errorCallback?.(error)
  }
}

export class Channel {
  constructor() {}
}
