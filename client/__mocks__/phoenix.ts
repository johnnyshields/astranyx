/**
 * Mock for phoenix package - used during testing
 */
import { vi } from 'vitest'

// Create mock channel that can be customized per test
const createMockChannel = () => ({
  on: vi.fn(),
  join: vi.fn().mockReturnValue({ receive: vi.fn().mockReturnThis() }),
  push: vi.fn().mockReturnValue({ receive: vi.fn().mockReturnThis() }),
  leave: vi.fn(),
})

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
    // Auto-trigger onOpen callback
    setTimeout(() => this._openCallback?.(), 0)
  }

  disconnect() {
    this._connected = false
    setTimeout(() => this._closeCallback?.(), 0)
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
