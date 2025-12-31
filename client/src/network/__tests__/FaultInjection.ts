/**
 * FaultInjection - Network fault simulation for Jepsen-style testing
 *
 * Provides tools to simulate:
 * - Network partitions (asymmetric and symmetric)
 * - Message loss (random, burst)
 * - Message delay (fixed, jitter, spike)
 * - Message reordering
 * - Connection drops
 *
 * Inspired by Jepsen's nemesis patterns:
 * https://jepsen.io/analyses
 */

import type { NetMessage } from '../types.ts'

// =============================================================================
// Types
// =============================================================================

export interface FaultConfig {
  /** Probability of dropping a message (0-1) */
  dropRate?: number
  /** Fixed delay in ms to add to all messages */
  fixedDelay?: number
  /** Random jitter to add (0 to jitter ms) */
  jitter?: number
  /** Probability of reordering with next message (0-1) */
  reorderRate?: number
  /** Whether this link is partitioned (no messages pass) */
  partitioned?: boolean
}

export interface LinkFaults {
  /** Faults from peer A to peer B */
  faults: Map<string, Map<string, FaultConfig>>
}

export type MessageInterceptor = (
  from: string,
  to: string,
  message: NetMessage
) => { drop: boolean; delay: number; message: NetMessage } | null

// =============================================================================
// Mock Data Channel
// =============================================================================

/**
 * MockDataChannel - Simulates RTCDataChannel with fault injection
 */
export class MockDataChannel {
  readonly label: string
  readyState: RTCDataChannelState = 'open'

  private messageQueue: Array<{ data: string; scheduledTime: number }> = []
  private reorderBuffer: Array<{ data: string; scheduledTime: number }> = []

  onmessage: ((event: { data: string }) => void) | null = null
  onopen: (() => void) | null = null
  onclose: (() => void) | null = null
  onerror: ((error: unknown) => void) | null = null

  private faultConfig: FaultConfig = {}
  private interceptor: MessageInterceptor | null = null
  private localPeerId: string
  private remotePeerId: string

  constructor(label: string, localPeerId: string, remotePeerId: string) {
    this.label = label
    this.localPeerId = localPeerId
    this.remotePeerId = remotePeerId
  }

  /**
   * Set fault configuration for this channel
   */
  setFaults(config: FaultConfig): void {
    this.faultConfig = config
  }

  /**
   * Set a custom message interceptor
   */
  setInterceptor(interceptor: MessageInterceptor): void {
    this.interceptor = interceptor
  }

  /**
   * Simulate sending a message
   */
  send(data: string): void {
    if (this.readyState !== 'open') {
      throw new Error('DataChannel is not open')
    }

    const message = JSON.parse(data) as NetMessage

    // Apply interceptor if set
    if (this.interceptor) {
      const result = this.interceptor(this.localPeerId, this.remotePeerId, message)
      if (result === null || result.drop) {
        return // Drop message
      }
      // Use modified message and delay
      this.scheduleDelivery(JSON.stringify(result.message), result.delay)
      return
    }

    // Apply fault config
    if (this.faultConfig.partitioned) {
      return // Partitioned, drop all messages
    }

    if (this.faultConfig.dropRate && Math.random() < this.faultConfig.dropRate) {
      return // Random drop
    }

    // Calculate delay
    let delay = 0
    if (this.faultConfig.fixedDelay) {
      delay += this.faultConfig.fixedDelay
    }
    if (this.faultConfig.jitter) {
      delay += Math.random() * this.faultConfig.jitter
    }

    // Handle reordering
    if (this.faultConfig.reorderRate && Math.random() < this.faultConfig.reorderRate) {
      this.reorderBuffer.push({ data, scheduledTime: Date.now() + delay })
      return
    }

    // Flush reorder buffer first
    if (this.reorderBuffer.length > 0) {
      for (const buffered of this.reorderBuffer) {
        this.scheduleDelivery(buffered.data, 0)
      }
      this.reorderBuffer = []
    }

    this.scheduleDelivery(data, delay)
  }

  /**
   * Schedule message delivery with delay
   */
  private scheduleDelivery(data: string, delay: number): void {
    if (delay <= 0) {
      this.deliverMessage(data)
    } else {
      setTimeout(() => this.deliverMessage(data), delay)
    }
  }

  /**
   * Deliver message to handler
   */
  private deliverMessage(data: string): void {
    if (this.readyState === 'open' && this.onmessage) {
      this.onmessage({ data })
    }
  }

  /**
   * Simulate closing the channel
   */
  close(): void {
    this.readyState = 'closed'
    this.onclose?.()
  }

  /**
   * Simulate connection drop
   */
  simulateDisconnect(): void {
    this.readyState = 'closed'
    this.onclose?.()
  }

  /**
   * Simulate reconnection
   */
  simulateReconnect(): void {
    this.readyState = 'open'
    this.onopen?.()
  }
}

// =============================================================================
// Fault Injection Controller
// =============================================================================

/**
 * FaultInjector - Controls fault injection across a network of peers
 */
export class FaultInjector {
  private channels: Map<string, Map<string, MockDataChannel>> = new Map()
  private globalFaults: FaultConfig = {}
  private linkFaults: Map<string, Map<string, FaultConfig>> = new Map()
  private partitions: Set<string>[] = []

  /**
   * Register a channel between two peers
   */
  registerChannel(from: string, to: string, channel: MockDataChannel): void {
    let fromChannels = this.channels.get(from)
    if (!fromChannels) {
      fromChannels = new Map()
      this.channels.set(from, fromChannels)
    }
    fromChannels.set(to, channel)

    // Apply any existing faults
    this.applyFaultsToChannel(from, to, channel)
  }

  /**
   * Get channel between two peers
   */
  getChannel(from: string, to: string): MockDataChannel | undefined {
    return this.channels.get(from)?.get(to)
  }

  /**
   * Set global faults (apply to all channels)
   */
  setGlobalFaults(config: FaultConfig): void {
    this.globalFaults = config
    this.applyAllFaults()
  }

  /**
   * Set faults for a specific link (from -> to)
   */
  setLinkFaults(from: string, to: string, config: FaultConfig): void {
    let fromFaults = this.linkFaults.get(from)
    if (!fromFaults) {
      fromFaults = new Map()
      this.linkFaults.set(from, fromFaults)
    }
    fromFaults.set(to, config)

    const channel = this.getChannel(from, to)
    if (channel) {
      this.applyFaultsToChannel(from, to, channel)
    }
  }

  /**
   * Create a network partition
   * Peers in different partition sets cannot communicate
   */
  createPartition(partitionSets: string[][]): void {
    this.partitions = partitionSets.map(set => new Set(set))
    this.applyAllFaults()
  }

  /**
   * Heal all partitions
   */
  healPartitions(): void {
    this.partitions = []
    this.applyAllFaults()
  }

  /**
   * Check if two peers are partitioned
   */
  arePartitioned(from: string, to: string): boolean {
    if (this.partitions.length === 0) return false

    for (const partition of this.partitions) {
      if (partition.has(from) && !partition.has(to)) {
        return true
      }
    }
    return false
  }

  /**
   * Simulate a burst of packet loss
   */
  async simulateLossBurst(durationMs: number, dropRate: number): Promise<void> {
    const originalFaults = { ...this.globalFaults }
    this.setGlobalFaults({ ...this.globalFaults, dropRate })

    await new Promise(resolve => setTimeout(resolve, durationMs))

    this.setGlobalFaults(originalFaults)
  }

  /**
   * Simulate a latency spike
   */
  async simulateLatencySpike(durationMs: number, addedDelay: number): Promise<void> {
    const originalFaults = { ...this.globalFaults }
    this.setGlobalFaults({
      ...this.globalFaults,
      fixedDelay: (this.globalFaults.fixedDelay ?? 0) + addedDelay,
    })

    await new Promise(resolve => setTimeout(resolve, durationMs))

    this.setGlobalFaults(originalFaults)
  }

  /**
   * Disconnect a specific peer from all others
   */
  disconnectPeer(peerId: string): void {
    // Disconnect all channels from this peer
    const fromChannels = this.channels.get(peerId)
    if (fromChannels) {
      for (const channel of fromChannels.values()) {
        channel.simulateDisconnect()
      }
    }

    // Disconnect all channels to this peer
    for (const [, toChannels] of this.channels) {
      const channel = toChannels.get(peerId)
      if (channel) {
        channel.simulateDisconnect()
      }
    }
  }

  /**
   * Reconnect a previously disconnected peer
   */
  reconnectPeer(peerId: string): void {
    const fromChannels = this.channels.get(peerId)
    if (fromChannels) {
      for (const channel of fromChannels.values()) {
        channel.simulateReconnect()
      }
    }

    for (const [, toChannels] of this.channels) {
      const channel = toChannels.get(peerId)
      if (channel) {
        channel.simulateReconnect()
      }
    }
  }

  /**
   * Clear all faults
   */
  clearAllFaults(): void {
    this.globalFaults = {}
    this.linkFaults.clear()
    this.partitions = []
    this.applyAllFaults()
  }

  /**
   * Apply faults to a specific channel
   */
  private applyFaultsToChannel(from: string, to: string, channel: MockDataChannel): void {
    const linkFault = this.linkFaults.get(from)?.get(to) ?? {}
    const isPartitioned = this.arePartitioned(from, to)

    channel.setFaults({
      ...this.globalFaults,
      ...linkFault,
      partitioned: isPartitioned || linkFault.partitioned || this.globalFaults.partitioned,
    })
  }

  /**
   * Apply faults to all channels
   */
  private applyAllFaults(): void {
    for (const [from, toChannels] of this.channels) {
      for (const [to, channel] of toChannels) {
        this.applyFaultsToChannel(from, to, channel)
      }
    }
  }
}

// =============================================================================
// Test Helpers
// =============================================================================

/**
 * Create a fully connected network of mock peers
 */
export function createMockNetwork(peerIds: string[]): {
  injector: FaultInjector
  channels: Map<string, Map<string, MockDataChannel>>
} {
  const injector = new FaultInjector()
  const channels = new Map<string, Map<string, MockDataChannel>>()

  for (const from of peerIds) {
    const fromChannels = new Map<string, MockDataChannel>()
    channels.set(from, fromChannels)

    for (const to of peerIds) {
      if (from === to) continue

      const channel = new MockDataChannel(`${from}->${to}`, from, to)
      fromChannels.set(to, channel)
      injector.registerChannel(from, to, channel)
    }
  }

  return { injector, channels }
}

/**
 * Scenario runner for Jepsen-style tests
 */
export interface TestScenario {
  name: string
  setup: (injector: FaultInjector) => void | Promise<void>
  run: (injector: FaultInjector) => void | Promise<void>
  verify: () => boolean | Promise<boolean>
  teardown?: (injector: FaultInjector) => void | Promise<void>
}

/**
 * Run a test scenario
 */
export async function runScenario(
  scenario: TestScenario,
  injector: FaultInjector
): Promise<{ passed: boolean; error?: Error }> {
  try {
    await scenario.setup(injector)
    await scenario.run(injector)
    const passed = await scenario.verify()
    await scenario.teardown?.(injector)
    return { passed }
  } catch (error) {
    await scenario.teardown?.(injector)
    return { passed: false, error: error as Error }
  }
}
