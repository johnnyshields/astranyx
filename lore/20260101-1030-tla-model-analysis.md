# TLA+ Model Analysis: Verification vs Reality

**Date**: 2026-01-01
**Scope**: Analysis of TLA+ formal models vs TypeScript implementation
**Files**: `tla/*.tla`, `client/src/network/*.ts`

---

## Executive Summary

This document provides a comprehensive analysis of the TLA+ formal verification models for the P2P lockstep netcode, comparing them against the actual TypeScript implementation to identify:

1. What the models genuinely verify (and what bugs they can catch)
2. Gaps between models and implementation
3. Contradictions between the 3 TLA+ models
4. Recommendations for keeping code and specs in sync

**Key Finding**: The TLA+ models provide strong verification of core safety properties (election safety, frame sync, event preservation) but do not model network unreliability, peer lifecycle, or checksum-based desync detection. The combination of TLA+ + Jepsen tests provides good coverage, but gaps remain.

---

## 1. Model Verification Value Assessment

### 1.1 What TLA+ Genuinely Verifies

| Model | Property | Value | What It Catches |
|-------|----------|-------|-----------------|
| All | `NoTwoLeadersInSameTerm` | HIGH | Split-brain bugs, duplicate leaders |
| All | `TypeInvariant` | MEDIUM | Variable bounds, type safety |
| LeaderElection | `EventuallyLeader` | HIGH | Liveness - system makes progress |
| LockstepCore/Full | `FrameBoundedDrift` | HIGH | Peers stay within 1 frame of each other |
| LockstepCore/Full | `LeaderUpToDate` | MEDIUM | Leader not too far behind |
| LockstepFull | `LocalEventsPreserved` | HIGH | Local events survive state sync |
| LockstepFull | `SyncTermBounded` | MEDIUM | No time-travel in sync terms |

**State space explored**:
- LeaderElection: ~15M states (5 peers, MaxTerm=3)
- LockstepCore: ~10M+ states (5 peers, MaxFrame=3, MaxTerm=2)
- LockstepFull: ~50M+ states (3 peers, MaxFrame=2, MaxTerm=2, MaxEvents=2)

### 1.2 What TLA+ Cannot Catch

| Category | Why Not Modeled | Real Bug Risk |
|----------|-----------------|---------------|
| **Network message loss** | Messages are atomic (instant delivery) | Lost heartbeats, lost votes, lost inputs |
| **Message reordering** | No message buffer abstraction | Stale messages processed out of order |
| **Timing bugs** | Boolean `heartbeatReceived` vs timestamp arithmetic | Off-by-one in timeout, jitter bugs |
| **InputBuffer bugs** | Not modeled at all | Frame-indexed storage, checksum validation |
| **Checksum mismatches** | No checksums in models | Desync detection failures |
| **Peer lifecycle** | Static peer set assumed | Join/leave/reconnect races |
| **WebRTC states** | No connection abstraction | Connection state machine bugs |
| **Callback ordering** | Actions are atomic | Reentrancy, ordering bugs |

### 1.3 Verification Confidence Rating

| Aspect | TLA+ | Tests | Combined | Notes |
|--------|------|-------|----------|-------|
| Election safety | 9/10 | 7/10 | 9/10 | Formally proven |
| Frame synchronization | 8/10 | 6/10 | 8/10 | Formally proven |
| Event preservation | 8/10 | 7/10 | 8/10 | LockstepFull only |
| Network failures | 0/10 | 8/10 | 6/10 | Jepsen tests only |
| Peer lifecycle | 0/10 | 5/10 | 4/10 | Partial test coverage |
| Desync recovery | 0/10 | 7/10 | 5/10 | Tests only |
| **Overall** | **5/10** | **7/10** | **7/10** | Good but gaps remain |

---

## 2. State Variable Comparison

### 2.1 Variables in Both TypeScript and TLA+

| Variable | TypeScript Location | TLA+ Variable | Model |
|----------|-------------------|---------------|-------|
| `currentFrame` | `LockstepNetcode.currentFrame:61` | `frame` | Core, Full |
| `confirmedFrame` | `LockstepNetcode.confirmedFrame:62` | Implicit (MinFrame) | Core, Full |
| `inputsReceived` | `InputBuffer.buffer` | `inputsReceived` | Core, Full |
| `currentTerm` | `LeaderElection.currentTerm:41` | `currentTerm` | All |
| `state` | `LeaderElection.state:42` | `state` | All |
| `votedFor` | `LeaderElection.votedFor:43` | `votedFor` | All |
| `votesReceived` | `LeaderElection.votesReceived:47` | `votesReceived` | All |
| `currentLeader` | `LeaderElection.currentLeader:44` | `CurrentLeader` (helper) | All |
| `pendingEvents` | `LocalEventQueue.pendingEvents:31` | `pendingEvents` | Full |
| `lastSyncedFrame` | `StateSyncManager.lastSyncFrame:28` | `syncTerm` | Full |
| `heartbeatReceived` | `LeaderElection.lastHeartbeat:49` | `heartbeatReceived` | All |

### 2.2 Variables in TypeScript but NOT in TLA+ (High Priority)

| Variable | TypeScript Location | Purpose | Bug Risk |
|----------|-------------------|---------|----------|
| `waitingForInputs` | `LockstepNetcode.ts:77` | Block frame advance | Could advance without all inputs |
| `checksumBuffer` | `InputBuffer.ts` (implicit) | Desync detection | Desync goes undetected |
| `desyncDetected` | `StateSyncManager.ts:31` | Trigger immediate sync | Delayed desync response |
| `lastHeartbeat` | `LeaderElection.ts:49` | Timestamp for timeout | Timeout arithmetic bugs |
| `electionTimer` | `LeaderElection.ts:48` | setTimeout handle | Timer cleanup races |
| `heartbeatTimer` | `LeaderElection.ts:50` | setInterval handle | Timer cleanup races |
| `peerLastSeen` | `LeaderElection.ts:54` | Per-peer liveness | Peer failure detection |
| `connectedPeers` | `LeaderElection.ts:53` | Active peer tracking | Partition handling |

### 2.3 Variables in TypeScript but NOT in TLA+ (Medium Priority)

| Variable | TypeScript Location | Purpose |
|----------|-------------------|---------|
| `running` | `LockstepNetcode.ts:76` | Start/stop state |
| `peers` (Map) | `LockstepNetcode.ts:65` | RTCDataChannel management |
| `timestamp` | `LocalEventQueue.ts:23` | Event timing debug |
| `config` | All classes | Configuration parameters |
| `inputDelay` | `LockstepConfig` | Latency hiding |
| `retentionFrames` | `InputBufferConfig` | Memory management |

---

## 3. Action/Operation Comparison

### 3.1 Operations in Both TypeScript and TLA+

| Operation | TypeScript Method | TLA+ Action | File:Line |
|-----------|------------------|-------------|-----------|
| Submit input | `tick()` | `SubmitInput(p)` | LockstepNetcode.ts:213 |
| Advance frame | `tryAdvanceFrame()` | `AdvanceFrame(p)` | LockstepNetcode.ts:250 |
| Generate event | `eventQueue.addEvents()` | `GenerateEvent(p)` | LocalEventQueue.ts:70 |
| Send state sync | `broadcastStateSync()` | `SendStateSync(leader)` | LockstepNetcode.ts:335 |
| Receive state sync | `receiveStateSync()` | `ReceiveStateSync(f, l)` | LockstepNetcode.ts:357 |
| Start election | `startElection()` | `StartElection(p)` | LeaderElection.ts:252 |
| Vote | `handleVoteRequest()` | `Vote(voter, candidate)` | LeaderElection.ts:288 |
| Become leader | `becomeLeader()` | `BecomeLeader(p)` | LeaderElection.ts:361 |
| Step down | `stepDown()` | `StepDown(p)` | LeaderElection.ts:376 |
| Broadcast heartbeat | `broadcastHeartbeat()` | `BroadcastHeartbeat(leader)` | LeaderElection.ts:396 |
| Expire heartbeat | Timer callback | `ExpireHeartbeat(p)` | LeaderElection.ts:184 |
| Retry election | Timer restart | `RetryElection(p)` | LeaderElection.ts:280 |

### 3.2 Operations in TypeScript but NOT in TLA+

#### Network Layer (Critical Gap)

| Operation | TypeScript Method | Purpose |
|-----------|------------------|---------|
| Add peer | `LockstepNetcode.addPeer()` | Register RTCDataChannel |
| Remove peer | `LockstepNetcode.removePeer()` | Unregister peer |
| Handle message | `handleMessage()` | Parse/route network messages |
| Broadcast input | `broadcastInput()` | Send input to all peers |
| Send to peer | `sendToPeer()` | Unicast message |
| WebRTC handshake | `P2PManager.connectToPeer()` | SDP/ICE exchange |

#### Timeout Management (Critical Gap)

| Operation | TypeScript Method | Purpose |
|-----------|------------------|---------|
| Start timers | `LeaderElection.start()` | Initialize timers |
| Stop timers | `LeaderElection.stop()` | Cleanup timers |
| Randomize timeout | `startElectionTimer()` | Jitter for split vote prevention |
| Check timeout | Timer callback | `Date.now() - lastHeartbeat` comparison |

#### Desync Detection (Critical Gap)

| Operation | TypeScript Method | Purpose |
|-----------|------------------|---------|
| Check desync | `checkForDesync()` | Compare checksums |
| Mark desync | `StateSyncManager.markDesync()` | Flag for immediate sync |
| Clear desync | `StateSyncManager.clearDesync()` | Reset after sync sent |
| Store checksum | `InputBuffer.storeInput()` | Save checksum with input |

### 3.3 Operations in TLA+ but NOT directly in TypeScript

| Operation | TLA+ Action | Notes |
|-----------|-------------|-------|
| `ForceLeaderChange(old, new)` | Models network events | Abstract - no direct implementation |

---

## 4. Model Contradictions

### 4.1 CONTRADICTION: Vote Frame Check

**LeaderElection.tla:79-81** (NO frame check):
```tla
Vote(voter, candidate) ==
    /\ state[candidate] = "Candidate"
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ \/ votedFor[voter] = 0
       \/ currentTerm[candidate] > currentTerm[voter]
```

**LockstepCore.tla:114-117** and **LockstepFull.tla:147-150** (HAS frame check):
```tla
Vote(voter, candidate) ==
    /\ state[candidate] = "Candidate"
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ frame[candidate] >= frame[voter]  \\* ADDITIONAL CHECK
    /\ \/ votedFor[voter] = 0
       \/ currentTerm[candidate] > currentTerm[voter]
```

**TypeScript implementation (LeaderElection.ts:300-304)**:
```typescript
if (
  message.term >= this.currentTerm &&
  (this.votedFor === null || this.votedFor === message.candidateId) &&
  message.lastFrame >= this.currentFrame  // HAS FRAME CHECK
) {
```

**Impact**: LeaderElection.tla could verify scenarios where a lagging peer becomes leader, which the implementation prevents. **LeaderElection.tla is incomplete**.

### 4.2 CONTRADICTION: State Sync Semantics

**LockstepCore.tla:82-85** (Atomic broadcast + apply):
```tla
SendStateSync(leader) ==
    /\ IsLeader(leader)
    /\ hasPendingEvent' = [p \in Peer |-> IF p = leader THEN hasPendingEvent[p] ELSE FALSE]
    /\ UNCHANGED <<frame, inputsReceived, currentTerm, state, votedFor, votesReceived, heartbeatReceived>>
```

**LockstepFull.tla:95-111** (Separate send and receive):
```tla
SendStateSync(leader) ==
    /\ IsLeader(leader)
    /\ syncTerm' = [p \in Peer |-> currentTerm[leader]]
    /\ UNCHANGED pendingEvents

ReceiveStateSync(follower, leader) ==
    /\ ~IsLeader(follower)
    /\ IsLeader(leader)
    /\ currentTerm[leader] >= syncTerm[follower]  \\* Term validation!
    /\ syncTerm' = [syncTerm EXCEPT ![follower] = currentTerm[leader]]
    /\ pendingEvents' = [pendingEvents EXCEPT
         ![follower] = {e \in pendingEvents[follower] : e[1] = follower}]
```

**Impact**: LockstepCore models synchronous state sync (unrealistic), while LockstepFull models asynchronous with term validation. LockstepCore could miss:
- Stale sync from outdated leader
- Race conditions between send and receive
- Out-of-order sync messages

### 4.3 Minor Inconsistency: Heartbeat Self-Receive

All 3 models set `heartbeatReceived[p] = TRUE` for ALL peers during BroadcastHeartbeat, including the leader itself.

**TypeScript (LeaderElection.ts:406-408)**:
```typescript
for (const peerId of this.connectedPeers) {
  this.sendMessage?.(peerId, heartbeat)
}
```

The leader does NOT receive its own heartbeat. Minor impact but technically inaccurate.

---

## 5. Network Failure Coverage

### 5.1 Failure Modes in Jepsen Tests but NOT in TLA+

| Scenario | Test Location | TLA+ Coverage |
|----------|--------------|---------------|
| Asymmetric partition (A→B but not B→A) | `jepsen.test.ts:845` | NOT modeled |
| Random packet loss (50%) | `jepsen.test.ts:933` | NOT modeled |
| Burst loss (100% temporary) | `jepsen.test.ts:956` | NOT modeled |
| Message reordering | `FaultInjection.ts:122` | NOT modeled |
| Partition healing | `FaultInjection.ts:256` | NOT modeled |
| Peer reconnection | `FaultInjection.ts:326` | NOT modeled |
| Latency spikes | `FaultInjection.ts:289` | NOT modeled |

### 5.2 Failure Modes in TLA+ but NOT explicitly tested

| Scenario | TLA+ Coverage | Test Coverage |
|----------|--------------|---------------|
| Arbitrary frame divergence | `FrameBoundedDrift` invariant | Implicit only |
| Multiple leaders in same term | `NoTwoLeadersInSameTerm` | Indirect tests |

### 5.3 Race Conditions in Code but NOT in TLA+

| Race Condition | Location | Description |
|----------------|----------|-------------|
| Callback ordering | All classes | Multiple callbacks in sequence |
| Start/stop during election | `LeaderElection.start()/stop()` | Timer cleanup during transition |
| Peer disconnect during vote | `removePeer()` + `Vote()` | Vote counted, peer gone |
| Concurrent state syncs | Multiple `ReceiveStateSync()` | Two syncs in flight |
| Checksum during sync | `tick()` + `receiveStateSync()` | Sync while computing checksum |
| Input cleanup during read | `cleanup()` + `getOrderedInputs()` | Frame cleaned while reading |
| Timer fires during reset | `reset()` + timer callback | Timer after state cleared |
| Credential refresh | `MultiplayerManager.ts:360` | TURN expires mid-game |

---

## 6. Code-Spec Synchronization

### 6.1 Current TLA+ Comments in Code

Good practice - the code has TLA+ mapping comments:

```typescript
// LockstepNetcode.ts:206-207
/**
 * Called each game tick with local input.
 * TLA+ model: SubmitInput(p) action - submits input and tries to advance frame.
 */
tick(localInput: PlayerInput, events?: GameEvent[], checksum?: number): boolean {

// LockstepNetcode.ts:249
/**
 * Try to advance to next frame if all inputs received.
 * TLA+ model: AdvanceFrame(p) action - advances when inputsReceived = Peer.
 */
private tryAdvanceFrame(): boolean {

// LeaderElection.ts:251
/**
 * Start an election (become candidate).
 * TLA+ model: StartElection(p) action - increments term, becomes candidate, votes for self.
 */
private startElection(): void {
```

### 6.2 Missing TLA+ Comments

| File | Missing Coverage |
|------|-----------------|
| `InputBuffer.ts` | No TLA+ comments - not modeled |
| `StateSyncManager.ts` | Partial - desync logic not modeled |
| `P2PManager.ts` | No TLA+ comments - not modeled |
| `LocalEventQueue.ts` | Partial - filtering logic only |

### 6.3 Recommendations for Sync

#### 1. Add Runtime Invariant Checks

```typescript
// In LeaderElection.ts - add after state changes
private assertInvariants(): void {
  // NoTwoLeadersInSameTerm (runtime check for debugging)
  if (process.env.NODE_ENV === 'development') {
    // Would need access to all election instances
    // For now, log warnings
    if (this.isLeader() && this.currentTerm === 0) {
      console.warn('TLA+ Invariant: Leader at term 0 (expected initial state)')
    }
  }
}
```

#### 2. Add TLA+ Markers to Critical Sections

```typescript
// Example for InputBuffer.ts
/**
 * TLA+ model: Part of SubmitInput(p) - stores input in buffer
 * Invariant: hasAllInputs(frame) iff inputsReceived[frame] = Peer
 */
storeInput(frameInput: FrameInput): void {
```

#### 3. Property-Based Tests

```typescript
// Using fast-check for property-based testing
import * as fc from 'fast-check'

describe('TLA+ Properties', () => {
  it('NoTwoLeadersInSameTerm', () => {
    fc.assert(fc.property(
      fc.array(electionActionArb, { minLength: 1, maxLength: 100 }),
      (actions) => {
        const elections = setupElections(['p1', 'p2', 'p3'])
        actions.forEach(action => applyAction(elections, action))

        // Check invariant
        const leadersByTerm = new Map<number, string[]>()
        elections.forEach(e => {
          if (e.isLeader()) {
            const term = e.getCurrentTerm()
            const leaders = leadersByTerm.get(term) || []
            leaders.push(e.getDebugInfo().leader!)
            leadersByTerm.set(term, leaders)
          }
        })

        return Array.from(leadersByTerm.values()).every(leaders => leaders.length <= 1)
      }
    ))
  })
})
```

#### 4. Fix LeaderElection.tla

Add frame check to match implementation:

```tla
Vote(voter, candidate) ==
    /\ state[candidate] = "Candidate"
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ frame[candidate] >= frame[voter]  \* ADD THIS LINE
    /\ \/ votedFor[voter] = 0
       \/ currentTerm[candidate] > currentTerm[voter]
```

**Note**: This requires adding `frame` variable to LeaderElection.tla or keeping it as election-only model and relying on LockstepCore/Full for frame checks.

---

## 7. Recommended TLA+ Improvements

### 7.1 High Priority

#### Model Message Loss

```tla
\* Add message buffer abstraction
VARIABLE messageQueue  \* Set of in-flight messages

SendMessage(from, to, msg) ==
    /\ messageQueue' = messageQueue \union {<<from, to, msg>>}

DeliverMessage(from, to, msg) ==
    /\ <<from, to, msg>> \in messageQueue
    /\ messageQueue' = messageQueue \ {<<from, to, msg>>}
    \* Process message...

DropMessage(from, to, msg) ==
    /\ <<from, to, msg>> \in messageQueue
    /\ messageQueue' = messageQueue \ {<<from, to, msg>>}
    \* Message lost - no processing
```

#### Model Peer Dynamics

```tla
VARIABLE peerStatus  \* [Peer -> {"connected", "disconnected"}]

DisconnectPeer(p) ==
    /\ peerStatus[p] = "connected"
    /\ peerStatus' = [peerStatus EXCEPT ![p] = "disconnected"]
    \* Trigger election if was leader
    /\ IF p = CurrentLeader THEN ... ELSE ...

ReconnectPeer(p) ==
    /\ peerStatus[p] = "disconnected"
    /\ peerStatus' = [peerStatus EXCEPT ![p] = "connected"]
```

#### Model Desync Detection

```tla
VARIABLE checksum  \* [Peer -> [Frame -> Int]]

CheckDesync(p, frame) ==
    /\ \E q \in Peer : checksum[p][frame] # checksum[q][frame]
    /\ desyncDetected' = TRUE
    \* Trigger immediate sync
```

### 7.2 Medium Priority

- Model reset/cleanup sequences
- Add bounded buffer verification
- Model concurrent state syncs
- Refine heartbeat timing (counter vs boolean)

---

## 8. Summary Tables

### 8.1 Coverage Matrix

| Category | TypeScript | TLA+ | Jepsen Tests | Combined |
|----------|-----------|------|--------------|----------|
| Core Lockstep | YES | YES | YES | STRONG |
| Leader Election | YES | YES | YES | STRONG |
| State Sync | YES | YES | YES | STRONG |
| Owner-Auth Events | YES | YES | YES | STRONG |
| Desync Detection | YES | NO | YES | MEDIUM |
| Message Loss | YES | NO | YES | MEDIUM |
| Peer Join/Leave | YES | NO | PARTIAL | WEAK |
| Timeout Arithmetic | YES | ABSTRACTED | PARTIAL | WEAK |
| Randomized Timeouts | YES | NO | NO | WEAK |
| WebRTC Lifecycle | YES | NO | NO | WEAK |

### 8.2 Model Comparison

| Aspect | LeaderElection | LockstepCore | LockstepFull |
|--------|---------------|--------------|--------------|
| Variables | 5 | 8 | 9 |
| Peers | 5 | 5 | 3 |
| States | ~15M | ~10M+ | ~50M+ |
| Time | ~3 min | ~3 min | ~10+ min |
| Frame check in Vote | NO | YES | YES |
| State sync | N/A | Atomic | Async |
| Events | N/A | Boolean | Tuples |
| SyncTerm | N/A | NO | YES |
| ForceLeaderChange | NO | NO | YES |

### 8.3 Contradiction Summary

| Issue | Models Affected | Fix Required |
|-------|-----------------|--------------|
| Missing frame check in Vote | LeaderElection.tla | Add frame variable or rely on other models |
| Atomic vs async state sync | LockstepCore vs LockstepFull | Document difference, use LockstepFull for realistic verification |
| Self-heartbeat | All 3 models | Minor - cosmetic fix |

---

## 9. Conclusions

### What the TLA+ Models DO Well

1. **Prove election safety** - No split-brain possible (formally verified)
2. **Verify frame synchronization** - Bounded drift guaranteed
3. **Ensure event preservation** - Local events survive state sync (LockstepFull)
4. **Catch logical errors** - Term monotonicity, majority requirements

### What the TLA+ Models DON'T Cover

1. **Network unreliability** - Message loss, reordering, delays
2. **Peer lifecycle** - Join, leave, reconnect
3. **Timing** - Actual timeout arithmetic, randomization
4. **Implementation details** - InputBuffer, checksums, WebRTC

### Recommended Actions

1. **Fix LeaderElection.tla** - Add frame check or document as election-only
2. **Add runtime invariants** - Check TLA+ properties in development mode
3. **Extend Jepsen tests** - Long-running chaos tests (5+ minutes)
4. **Consider property-based tests** - fast-check for random trace verification
5. **Document abstraction gaps** - Clear notes on what TLA+ doesn't model

### Overall Assessment

**The TLA+ models are NOT "faking it"** - they genuinely verify important safety properties through exhaustive state exploration. However, they verify an **abstraction** of the system, not the implementation itself.

**Confidence level**: 7/10 for correctness under normal conditions, 5/10 for correctness under adversarial network conditions.

**The combination of TLA+ + unit tests + Jepsen tests provides solid coverage**, but formalizing network behavior in TLA+ would significantly increase confidence.

---

## Appendix: File References

| File | Purpose | TLA+ Coverage |
|------|---------|---------------|
| `LockstepNetcode.ts:1-481` | Main orchestrator | Good |
| `LeaderElection.ts:1-580` | Raft-style election | Good |
| `StateSyncManager.ts:1-221` | State sync coordination | Partial |
| `LocalEventQueue.ts:1-185` | Event buffering | Partial |
| `InputBuffer.ts:1-150` | Frame-indexed inputs | NOT MODELED |
| `P2PManager.ts:1-334` | WebRTC management | NOT MODELED |
| `types.ts` | Type definitions | N/A |
| `__tests__/LockstepNetcode.jepsen.test.ts` | Chaos tests | N/A |
| `__tests__/FaultInjection.ts` | Fault injection utils | N/A |
