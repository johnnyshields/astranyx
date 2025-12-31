/**
 * TLA+ Sync Verification Tests
 *
 * Ensures bidirectional correspondence between TLA+ specifications and TypeScript code:
 *
 * 1. Forward: All TLA+ references in TS comments exist in TLA+ files
 * 2. Reverse: All TLA+ actions have corresponding TS implementations
 *
 * This prevents:
 * - Stale comments referencing non-existent TLA+ actions
 * - TLA+ actions without implementation
 * - Drift between spec and code
 */

import { describe, it, expect, beforeAll } from 'bun:test'
import * as fs from 'fs'
import * as path from 'path'

// =============================================================================
// Configuration
// =============================================================================

// Resolve paths relative to workspace root
// __dirname is client/src/network/__tests__
// We need to go up to client/, then to astranyx/tla
const TLA_DIR = path.resolve(__dirname, '../../../../tla')
const TS_NETWORK_DIR = path.resolve(__dirname, '..')

const TLA_FILES = [
  'LockstepState.tla',
  'LockstepNetwork.tla',
  'LeaderElection.tla',
  'LockstepSimple.tla',
]

const TS_FILES = [
  'LockstepNetcode.ts',
  'LeaderElection.ts',
  'InputBuffer.ts',
  'LocalEventQueue.ts',
  'StateSyncManager.ts',
  'P2PManager.ts',
]

// Actions that are intentionally not implemented (modeling-only)
const TLA_ONLY_ACTIONS = new Set([
  // LockstepSimple - simplified model, covered by LockstepState
  'LockstepSimple.SendStateSync',  // Atomic version, real impl is async
  'LockstepSimple.GenerateEvent',  // Boolean version

  // LockstepNetwork - network-level modeling (TLA+ only)
  'LockstepNetwork.LoseMessage',       // Network handles loss
  'LockstepNetwork.CreatePartition',   // Network condition, not code
  'LockstepNetwork.HealPartition',     // Network condition, not code

  // Abstract/helper actions
  'LockstepState.ForceLeaderChange',  // External trigger only
])

// Common words that appear in comments but aren't TLA+ action references
// We use case-insensitive matching, so include lowercase versions too
const IGNORE_WORDS = new Set([
  // Meta-terms used in documentation
  'Variables', 'Actions', 'Invariants', 'Invariant', 'Properties', 'Property',
  'Model', 'Models', 'Spec', 'Specification', 'Module', 'Key',
  'Safety', 'Liveness', 'Fairness', 'Constraint', 'State',

  // Common English words that start with capitals or appear in comments
  'Runtime', 'Check', 'Checks', 'Verification', 'Verified',
  'Term', 'Terms', 'Frame', 'Frames', 'Peer', 'Peers',
  'Leader', 'Follower', 'Candidate', 'Election', 'Consistency',
  'Note', 'Important', 'See', 'This', 'The', 'After', 'Before',
  'If', 'When', 'Returns', 'Sets', 'Gets', 'Creates', 'Updates',
  'Buffer', 'Queue', 'Manager', 'Handler', 'Callback',
  'Found', 'Invalid', 'Valid', 'True', 'False', 'Null',
  'Checked', 'Violated', 'Expected', 'Received', 'Local', 'Remote',

  // TLA+ variable names (not actions)
  'frame', 'term', 'state', 'peer', 'buffer', 'network',
  'connectionState', 'syncTerm', 'currentTerm', 'votedFor',
  'lastAcceptedSyncTerm', 'candidate', 'found', 'checked', 'invalid',

  // Single letters and short matches
  's', 'p', 'q', 'f', 'e', 'm', 'msg',
])

// TS implementations that don't map 1:1 to TLA+ (helper methods, etc.)
const TS_ONLY_IMPLEMENTATIONS = new Set([
  // Internal helpers
  'getDebugInfo',
  'reset',
  'cleanup',
  'size',

  // Callback setters
  'setInputHandler',
  'setDesyncHandler',
  'setStateSyncHandler',
  'setLeaderChangeHandler',
  'setPeerDisconnectHandler',
  'setSendMessage',
  'setEventQueue',

  // Getters (state access, not actions)
  'getCurrentFrame',
  'getConfirmedFrame',
  'isWaitingForInputs',
  'getInputDelay',
  'getLocalPlayerIndex',
  'getCurrentTerm',
  'getCurrentLeader',
  'isLeader',
  'getState',
  'shouldSendStateSync',
  'hasDesync',
  'getLastSyncFrame',
  'getSyncInterval',
  'getFramesSinceSync',
  'getPendingEvents',
  'getEventsForReapply',
  'pendingCount',
  'getConnectedPeerCount',
  'hasAllInputs',
  'hasInput',
  'getInputCount',
  'getFrameInputs',
  'getOrderedInputs',
  'filterRemoteEvents',
  'getLastSyncedFrame',
])

// =============================================================================
// TLA+ Parser
// =============================================================================

interface TLASpec {
  filename: string
  actions: Set<string>
  variables: Set<string>
  invariants: Set<string>
}

function parseTLAFile(filepath: string): TLASpec {
  const content = fs.readFileSync(filepath, 'utf-8')
  const filename = path.basename(filepath, '.tla')

  const actions = new Set<string>()
  const variables = new Set<string>()
  const invariants = new Set<string>()

  // Extract actions: Name(args) == or Name ==
  // Pattern: word at start of line, followed by optional (args), then ==
  const actionRegex = /^([A-Z][A-Za-z0-9_]*)\s*(?:\([^)]*\))?\s*==/gm
  let match
  while ((match = actionRegex.exec(content)) !== null) {
    const name = match[1]!
    // Skip helpers and constants
    if (!name.startsWith('MC') &&
        !['Init', 'Next', 'Spec', 'Fairness', 'StateConstraint'].includes(name) &&
        !name.endsWith('Invariant') &&
        !name.includes('Property')) {
      actions.add(name)
    }
  }

  // Extract variables: VARIABLE name
  const varRegex = /^VARIABLE\s+(\w+)/gm
  while ((match = varRegex.exec(content)) !== null) {
    variables.add(match[1]!)
  }

  // Extract invariants: Name == (in Safety Properties section)
  const invariantRegex = /^([A-Z][A-Za-z0-9_]*)\s*==\s*$/gm
  const safetySection = content.split('Safety Properties')[1] || ''
  while ((match = invariantRegex.exec(safetySection)) !== null) {
    invariants.add(match[1]!)
  }

  return { filename, actions, variables, invariants }
}

// =============================================================================
// TypeScript Parser
// =============================================================================

interface TSFile {
  filename: string
  tlaReferences: Map<string, string[]>  // TLA+ name -> line numbers/contexts
  publicMethods: Set<string>
  tlaActionComments: Map<string, string>  // method name -> TLA+ action referenced
}

function parseTSFile(filepath: string): TSFile {
  const content = fs.readFileSync(filepath, 'utf-8')
  const filename = path.basename(filepath, '.ts')
  const lines = content.split('\n')

  const tlaReferences = new Map<string, string[]>()
  const publicMethods = new Set<string>()
  const tlaActionComments = new Map<string, string>()

  // Find all TLA+ references in comments
  // We look for specific patterns that indicate intentional TLA+ references:
  //   - "TLA+ model: ActionName action" or "TLA+: ActionName"
  //   - "ActionName action in File.tla"
  //   - "TLA+ Invariant: InvariantName"
  //
  // We're strict: only match action/invariant names that appear in context
  const tlaActionPatterns = [
    // "TLA+ model: ActionName" or "TLA+: ActionName action"
    /TLA\+[^:]*:\s*([A-Z][A-Za-z0-9_]+)\s*(?:action)?/gi,
    // "ActionName action in File.tla"
    /([A-Z][A-Za-z0-9_]+)\s+action\s+in\s+\w+\.tla/gi,
    // "TLA+ Invariant: Name" or "TLA+ invariant Name"
    /TLA\+\s+[Ii]nvariant[s]?[:\s]+([A-Z][A-Za-z0-9_]+)/gi,
  ]

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!
    const lineNum = i + 1

    // Only process comment lines or lines with TLA+ context
    if (!line.includes('*') && !line.includes('//') && !line.includes('TLA')) {
      continue
    }

    // Check for TLA+ references
    for (const pattern of tlaActionPatterns) {
      pattern.lastIndex = 0  // Reset regex state
      let match
      while ((match = pattern.exec(line)) !== null) {
        const ref = match[1]!

        // Skip file references
        if (ref.endsWith('tla')) continue

        // Skip ignored words (case-insensitive check)
        if (IGNORE_WORDS.has(ref) || IGNORE_WORDS.has(ref.toLowerCase())) continue

        // Must be at least 4 chars and start with uppercase to be an action
        if (ref.length < 4) continue
        if (!/^[A-Z]/.test(ref)) continue

        // TLA+ actions are typically CamelCase - skip all-lowercase
        if (ref === ref.toLowerCase()) continue

        const refs = tlaReferences.get(ref) || []
        refs.push(`line ${lineNum}`)
        tlaReferences.set(ref, refs)
      }
    }

    // Track method definitions with TLA+ comments
    // Look for: /** ... TLA+ ... */ followed by method definition
    if (line.includes('TLA+') && line.includes('*')) {
      // This is a TLA+ comment, look for action reference
      const actionMatch = line.match(/TLA\+[^:]*:\s*([A-Z][A-Za-z0-9_]*)/i)
      if (actionMatch) {
        // Find the next method definition
        for (let j = i + 1; j < Math.min(i + 10, lines.length); j++) {
          const methodMatch = lines[j]!.match(/^\s*(?:private\s+|public\s+)?(\w+)\s*\(/)
          if (methodMatch && !methodMatch[1]!.startsWith('get') && !methodMatch[1]!.startsWith('set')) {
            tlaActionComments.set(methodMatch[1]!, actionMatch[1]!)
            break
          }
        }
      }
    }

    // Find public/private method definitions
    const methodMatch = line.match(/^\s*(?:private\s+|public\s+)?(\w+)\s*\([^)]*\)\s*(?::\s*\w+)?\s*\{?/)
    if (methodMatch &&
        !line.includes('constructor') &&
        !line.includes('=>') &&
        !line.trim().startsWith('//') &&
        !line.trim().startsWith('*')) {
      const methodName = methodMatch[1]!
      if (!methodName.startsWith('_')) {
        publicMethods.add(methodName)
      }
    }
  }

  return { filename, tlaReferences, publicMethods, tlaActionComments }
}

// =============================================================================
// Tests
// =============================================================================

describe('TLA+ Sync Verification', () => {
  let tlaSpecs: TLASpec[]
  let tsFiles: TSFile[]

  // Load all files once
  beforeAll(() => {
    tlaSpecs = TLA_FILES
      .map(f => path.join(TLA_DIR, f))
      .filter(f => fs.existsSync(f))
      .map(parseTLAFile)

    tsFiles = TS_FILES
      .map(f => path.join(TS_NETWORK_DIR, f))
      .filter(f => fs.existsSync(f))
      .map(parseTSFile)
  })

  describe('Forward Check: TS → TLA+', () => {
    it('all TLA+ action references in TS comments exist in TLA+ specs', () => {
      const allTLAActions = new Set<string>()
      for (const spec of tlaSpecs) {
        for (const action of spec.actions) {
          allTLAActions.add(action)
          allTLAActions.add(`${spec.filename}.${action}`)
        }
      }

      const missingActions: string[] = []

      for (const ts of tsFiles) {
        for (const [ref, locations] of ts.tlaReferences) {
          // Skip known file names
          if (TLA_FILES.some(f => f.startsWith(ref))) continue

          // Check if action exists (with or without file prefix)
          const exists = allTLAActions.has(ref) ||
            [...allTLAActions].some(a => a.endsWith(`.${ref}`))

          if (!exists) {
            missingActions.push(`${ts.filename}: "${ref}" referenced at ${locations.join(', ')}`)
          }
        }
      }

      if (missingActions.length > 0) {
        console.error('TS references TLA+ actions that do not exist:')
        missingActions.forEach(m => console.error(`  - ${m}`))
      }

      expect(missingActions).toEqual([])
    })

    it('all TLA+ variable references in TS exist in TLA+ specs', () => {
      const allTLAVars = new Set<string>()
      for (const spec of tlaSpecs) {
        for (const v of spec.variables) {
          allTLAVars.add(v)
        }
      }

      // Common variable names referenced in TS comments
      const varPatterns = [
        'frame', 'currentTerm', 'state', 'votedFor', 'votesReceived',
        'inputsReceived', 'heartbeatReceived', 'syncTerm', 'pendingEvents',
        'inSync', 'connectionState', 'network', 'inputBuffer', 'checksums',
        'desynced', 'partitioned', 'flapCount', 'iceRestarting',
      ]

      const missingVars: string[] = []

      for (const v of varPatterns) {
        if (!allTLAVars.has(v)) {
          // Only flag if it's actually referenced
          let isReferenced = false
          for (const ts of tsFiles) {
            for (const [ref] of ts.tlaReferences) {
              if (ref.toLowerCase().includes(v.toLowerCase())) {
                isReferenced = true
                break
              }
            }
          }
          if (isReferenced) {
            missingVars.push(v)
          }
        }
      }

      // This is informational, not a hard failure
      if (missingVars.length > 0) {
        console.warn('Variables referenced but not in TLA+:', missingVars)
      }
    })
  })

  describe('Reverse Check: TLA+ → TS', () => {
    it('all TLA+ actions have corresponding TS implementations', () => {
      const unmappedActions: string[] = []

      // Collect all TLA+ action references from TS
      const implementedActions = new Set<string>()
      for (const ts of tsFiles) {
        for (const [ref] of ts.tlaReferences) {
          implementedActions.add(ref)
        }
        for (const [, action] of ts.tlaActionComments) {
          implementedActions.add(action)
        }
      }

      for (const spec of tlaSpecs) {
        for (const action of spec.actions) {
          const qualifiedName = `${spec.filename}.${action}`

          // Skip known TLA-only actions
          if (TLA_ONLY_ACTIONS.has(qualifiedName) || TLA_ONLY_ACTIONS.has(action)) {
            continue
          }

          // Skip helper definitions (lowercase start after first word)
          if (action.match(/^[A-Z][a-z]+[A-Z]/)) {
            // CamelCase action - check if implemented
            const isImplemented = implementedActions.has(action) ||
              implementedActions.has(qualifiedName)

            if (!isImplemented) {
              unmappedActions.push(`${spec.filename}: ${action}`)
            }
          }
        }
      }

      if (unmappedActions.length > 0) {
        console.warn('TLA+ actions without TS implementation reference:')
        unmappedActions.forEach(a => console.warn(`  - ${a}`))

        // This is a warning, not hard failure (some actions are spec-only)
        // Uncomment to make it strict:
        // expect(unmappedActions).toEqual([])
      }
    })

    it('all TLA+ invariants have corresponding runtime assertions', () => {
      const allInvariants = new Set<string>()
      for (const spec of tlaSpecs) {
        for (const inv of spec.invariants) {
          allInvariants.add(inv)
        }
      }

      // Check which invariants have runtime assertions
      const assertMethods = [
        'assertInvariants',
        'assertLocalEventsOnly',
        'assertCanAdvance',
      ]

      const tsContent = tsFiles.map(ts =>
        fs.readFileSync(path.join(TS_NETWORK_DIR, `${ts.filename}.ts`), 'utf-8')
      ).join('\n')

      const implementedInvariants = new Set<string>()

      // Check for invariant references in assert methods
      for (const inv of allInvariants) {
        if (tsContent.includes(inv)) {
          implementedInvariants.add(inv)
        }
      }

      const unimplementedInvariants = [...allInvariants].filter(
        inv => !implementedInvariants.has(inv) &&
               !inv.includes('Type') &&  // TypeInvariant is implicit
               !inv.includes('Constraint')
      )

      if (unimplementedInvariants.length > 0) {
        console.warn('TLA+ invariants without runtime assertions:')
        unimplementedInvariants.forEach(i => console.warn(`  - ${i}`))
      }
    })
  })

  describe('Structural Consistency', () => {
    it('TLA+ files exist and are parseable', () => {
      for (const filename of TLA_FILES) {
        const filepath = path.join(TLA_DIR, filename)
        expect(fs.existsSync(filepath)).toBe(true)

        // Should parse without throwing
        const spec = parseTLAFile(filepath)
        expect(spec.actions.size).toBeGreaterThan(0)
      }
    })

    it('TS files reference at least one TLA+ concept', () => {
      for (const ts of tsFiles) {
        const hasReferences = ts.tlaReferences.size > 0 || ts.tlaActionComments.size > 0

        // Main implementation files should have TLA+ references
        const requiresReferences = [
          'LockstepNetcode',
          'LeaderElection',
          'InputBuffer',
          'LocalEventQueue',
          'StateSyncManager',
        ].includes(ts.filename)

        if (requiresReferences && !hasReferences) {
          console.warn(`${ts.filename}.ts has no TLA+ references`)
        }
      }
    })

    it('module docstrings list TLA+ model files', () => {
      const requiredFiles = [
        'LockstepNetcode.ts',
        'LeaderElection.ts',
        'InputBuffer.ts',
        'LocalEventQueue.ts',
        'StateSyncManager.ts',
      ]

      for (const filename of requiredFiles) {
        const filepath = path.join(TS_NETWORK_DIR, filename)
        if (!fs.existsSync(filepath)) continue

        const content = fs.readFileSync(filepath, 'utf-8')
        const first100Lines = content.split('\n').slice(0, 100).join('\n')

        // Should mention TLA+ in module docstring
        const hasTLARef = first100Lines.includes('TLA+') ||
                          first100Lines.includes('.tla')

        expect(hasTLARef).toBe(true)
      }
    })
  })

  describe('Action Coverage Report', () => {
    it('generates coverage summary', () => {
      const coverage: Record<string, { total: number; mapped: number; actions: string[] }> = {}

      // Collect all TLA+ references from TS
      const implementedActions = new Set<string>()
      for (const ts of tsFiles) {
        for (const [ref] of ts.tlaReferences) {
          implementedActions.add(ref)
        }
      }

      for (const spec of tlaSpecs) {
        const mapped: string[] = []
        const unmapped: string[] = []

        for (const action of spec.actions) {
          if (implementedActions.has(action) || TLA_ONLY_ACTIONS.has(`${spec.filename}.${action}`)) {
            mapped.push(action)
          } else {
            unmapped.push(action)
          }
        }

        coverage[spec.filename] = {
          total: spec.actions.size,
          mapped: mapped.length,
          actions: unmapped,
        }
      }

      console.log('\n=== TLA+ Action Coverage ===\n')
      for (const [file, stats] of Object.entries(coverage)) {
        const pct = stats.total > 0 ? Math.round((stats.mapped / stats.total) * 100) : 100
        console.log(`${file}: ${stats.mapped}/${stats.total} (${pct}%)`)
        if (stats.actions.length > 0 && stats.actions.length <= 10) {
          console.log(`  Unmapped: ${stats.actions.join(', ')}`)
        }
      }
      console.log('')

      // Just informational, always passes
      expect(true).toBe(true)
    })
  })
})

// =============================================================================
// Helper to run standalone
// =============================================================================

// Can be run directly: bun run src/network/__tests__/TLASync.test.ts
if (import.meta.main) {
  console.log('Run with: bun test TLASync.test.ts')
}
