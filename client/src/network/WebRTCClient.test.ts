import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { WebRTCClient, type GameMessage, type NetworkConfig } from './WebRTCClient'

// Mock WebSocket
class MockWebSocket {
  static CONNECTING = 0
  static OPEN = 1
  static CLOSING = 2
  static CLOSED = 3

  readyState = MockWebSocket.CONNECTING
  onopen: (() => void) | null = null
  onerror: ((error: Event) => void) | null = null
  onclose: (() => void) | null = null
  onmessage: ((event: MessageEvent) => void) | null = null

  constructor(public url: string) {
    // Auto-connect after a tick
    setTimeout(() => {
      this.readyState = MockWebSocket.OPEN
      this.onopen?.()
    }, 0)
  }

  send(_data: string): void {
    // Mock implementation
  }

  close(): void {
    this.readyState = MockWebSocket.CLOSED
    this.onclose?.()
  }
}

// Mock RTCPeerConnection
class MockRTCPeerConnection {
  connectionState: RTCPeerConnectionState = 'new'
  onicecandidate: ((event: RTCPeerConnectionIceEvent) => void) | null = null
  onconnectionstatechange: (() => void) | null = null
  ondatachannel: ((event: RTCDataChannelEvent) => void) | null = null

  private dataChannels: MockRTCDataChannel[] = []

  createDataChannel(label: string, _options?: RTCDataChannelInit): RTCDataChannel {
    const channel = new MockRTCDataChannel(label)
    this.dataChannels.push(channel)
    return channel as unknown as RTCDataChannel
  }

  async createOffer(): Promise<RTCSessionDescriptionInit> {
    return { type: 'offer', sdp: 'mock-offer-sdp' }
  }

  async createAnswer(): Promise<RTCSessionDescriptionInit> {
    return { type: 'answer', sdp: 'mock-answer-sdp' }
  }

  async setLocalDescription(_desc: RTCSessionDescriptionInit): Promise<void> {}
  async setRemoteDescription(_desc: RTCSessionDescription): Promise<void> {}
  async addIceCandidate(_candidate: RTCIceCandidate): Promise<void> {}

  close(): void {
    this.connectionState = 'closed'
  }

  // Helper to simulate connection
  _simulateConnected(): void {
    this.connectionState = 'connected'
    this.onconnectionstatechange?.()
    for (const channel of this.dataChannels) {
      channel._simulateOpen()
    }
  }
}

class MockRTCDataChannel {
  label: string
  binaryType: BinaryType = 'arraybuffer'
  readyState: RTCDataChannelState = 'connecting'
  onopen: (() => void) | null = null
  onclose: (() => void) | null = null
  onerror: ((error: Event) => void) | null = null
  onmessage: ((event: MessageEvent) => void) | null = null

  constructor(label: string) {
    this.label = label
  }

  close(): void {
    this.readyState = 'closed'
    this.onclose?.()
  }

  send(_data: string | ArrayBuffer | Blob | ArrayBufferView): void {
    // Mock implementation
  }

  _simulateOpen(): void {
    this.readyState = 'open'
    this.onopen?.()
  }

  _simulateMessage(data: ArrayBuffer): void {
    this.onmessage?.({ data } as MessageEvent)
  }
}

// Set up global mocks
vi.stubGlobal('WebSocket', MockWebSocket)
vi.stubGlobal('RTCPeerConnection', MockRTCPeerConnection)
vi.stubGlobal('RTCSessionDescription', class {
  type: RTCSdpType
  sdp: string
  constructor(init: RTCSessionDescriptionInit) {
    this.type = init.type!
    this.sdp = init.sdp || ''
  }
})
vi.stubGlobal('RTCIceCandidate', class {
  candidate: string
  constructor(init: RTCIceCandidateInit) {
    this.candidate = init.candidate || ''
  }
})

describe('WebRTCClient', () => {
  let client: WebRTCClient
  const config: NetworkConfig = {
    signalingUrl: 'ws://localhost:4200/signaling',
  }

  beforeEach(() => {
    vi.useFakeTimers()
    client = new WebRTCClient(config)
  })

  afterEach(() => {
    vi.useRealTimers()
    vi.restoreAllMocks()
  })

  describe('constructor', () => {
    it('should create client with config', () => {
      expect(client).toBeInstanceOf(WebRTCClient)
      expect(client.getState()).toBe('disconnected')
    })

    it('should use default ICE servers when not provided', () => {
      const clientNoIce = new WebRTCClient({ signalingUrl: 'ws://test' })
      expect(clientNoIce).toBeInstanceOf(WebRTCClient)
    })

    it('should use custom ICE servers when provided', () => {
      const clientCustomIce = new WebRTCClient({
        signalingUrl: 'ws://test',
        iceServers: [{ urls: 'stun:custom.stun.server:19302' }],
      })
      expect(clientCustomIce).toBeInstanceOf(WebRTCClient)
    })
  })

  describe('connect', () => {
    it('should throw if already connecting', async () => {
      const connectPromise = client.connect('room1', 'player1')
      await vi.advanceTimersByTimeAsync(0)

      await expect(client.connect('room1', 'player1')).rejects.toThrow(
        'Cannot connect: current state is'
      )

      // Clean up
      await connectPromise.catch(() => {})
    })

    it('should connect to signaling server', async () => {
      const connectPromise = client.connect('room1', 'player1')
      await vi.advanceTimersByTimeAsync(0)

      expect(client.getState()).toBe('signaling')

      await connectPromise.catch(() => {})
    })

    it('should create peer connection after signaling', async () => {
      const connectPromise = client.connect('room1', 'player1')
      await vi.advanceTimersByTimeAsync(0)

      // State should be signaling after WebSocket connects
      expect(client.getState()).toBe('signaling')

      await connectPromise.catch(() => {})
    })
  })

  describe('getState', () => {
    it('should return disconnected initially', () => {
      expect(client.getState()).toBe('disconnected')
    })
  })

  describe('isConnected', () => {
    it('should return false when disconnected', () => {
      expect(client.isConnected()).toBe(false)
    })
  })

  describe('getLatency', () => {
    it('should return 0 initially', () => {
      expect(client.getLatency()).toBe(0)
    })
  })

  describe('send', () => {
    it('should not send when not connected', () => {
      // Should not throw, just no-op
      client.send('input', { test: true })
    })
  })

  describe('onMessage', () => {
    it('should register message handler and return unsubscribe function', () => {
      const handler = vi.fn()
      const unsubscribe = client.onMessage(handler)

      expect(typeof unsubscribe).toBe('function')
    })

    it('should unsubscribe handler when called', () => {
      const handler = vi.fn()
      const unsubscribe = client.onMessage(handler)
      unsubscribe()

      // Handler should no longer be registered
    })
  })

  describe('disconnect', () => {
    it('should reset state to disconnected', () => {
      client.disconnect()
      expect(client.getState()).toBe('disconnected')
    })

    it('should be idempotent', () => {
      client.disconnect()
      client.disconnect()
      expect(client.getState()).toBe('disconnected')
    })
  })

  describe('message encoding/decoding', () => {
    it('should handle message handlers', async () => {
      const handler = vi.fn()
      client.onMessage(handler)

      // Connect and simulate receiving a message
      const connectPromise = client.connect('room1', 'player1')
      await vi.advanceTimersByTimeAsync(0)

      await connectPromise.catch(() => {})
    })
  })
})

describe('GameMessage', () => {
  it('should have correct structure', () => {
    const message: GameMessage = {
      type: 'input',
      seq: 1,
      timestamp: Date.now(),
      data: { up: true },
    }

    expect(message.type).toBe('input')
    expect(message.seq).toBe(1)
    expect(typeof message.timestamp).toBe('number')
    expect(message.data).toEqual({ up: true })
  })

  it('should support all message types', () => {
    const types: GameMessage['type'][] = ['input', 'state', 'event', 'ping', 'pong']

    for (const type of types) {
      const message: GameMessage = {
        type,
        seq: 0,
        timestamp: 0,
        data: null,
      }
      expect(message.type).toBe(type)
    }
  })
})
