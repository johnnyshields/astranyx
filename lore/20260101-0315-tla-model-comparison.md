# TLA+ Model Structure

Date: 2026-01-01

## Overview

The `tla/` directory contains TLA+ specifications for verifying the P2P lockstep netcode:

| Model | Purpose | Peers | States | Time |
|-------|---------|:-----:|--------|------|
| **LeaderElection** | Election only | 5 | ~15M+ | ~3 min |
| **LockstepCore** | Fast full check | 5 | ~10M+ | ~3 min |
| **LockstepFull** | Complete | 3 | ~50M+ | ~10+ min |

## LeaderElection

Pure Raft-style election model. Uses 5 peers for interesting majority scenarios (3-of-5).

**Variables (5):**
- `currentTerm` - election term per peer
- `state` - Follower/Candidate/Leader
- `votedFor` - vote tracking
- `votesReceived` - votes received by candidates
- `heartbeatReceived` - heartbeat tracking

**Properties:**
- `NoTwoLeadersInSameTerm` - election safety
- `TypeInvariant` - variable bounds
- `EventuallyLeader` - liveness

**Config:** `Peer={1,2,3,4,5}`, `MaxTerm=3`

## LockstepCore

Simplified model for fast iteration. Boolean events, atomic state sync.

**Variables (8):**
- `frame`, `inputsReceived` - lockstep
- `currentTerm`, `state`, `votedFor`, `votesReceived`, `heartbeatReceived` - election
- `hasPendingEvent` - events (boolean)

**Simplifications vs Full:**
- Events as boolean (not tuples)
- Atomic state sync (send+receive combined)
- No syncTerm tracking
- No ForceLeaderChange

**Config:** `Peer={1,2,3,4,5}`, `MaxFrame=3`, `MaxTerm=2`

## LockstepFull

Comprehensive model with all features.

**Variables (9):**
- `frame`, `inputsReceived` - lockstep
- `currentTerm`, `state`, `votedFor`, `votesReceived`, `heartbeatReceived` - election
- `syncTerm` - state sync term validation
- `pendingEvents` - events as `<<owner, frame>>` tuples

**Additional features:**
- Separate `SendStateSync` and `ReceiveStateSync` actions
- `syncTerm` for rejecting stale syncs
- `ForceLeaderChange` for network events
- `LocalEventsPreserved` invariant
- `SyncTermBounded` invariant

**Config:** `Peer={1,2,3}`, `MaxFrame=2`, `MaxTerm=2`, `MaxEvents=2`

## Properties Verified

All models verify:
- **NoTwoLeadersInSameTerm** - election safety
- **TypeInvariant** - variable bounds

LockstepCore/Full additionally verify:
- **FrameBoundedDrift** - lockstep (max 1 frame apart)
- **LeaderUpToDate** - leader reasonably current

LockstepFull additionally verifies:
- **LocalEventsPreserved** - local events survive state sync
- **SyncTermBounded** - sync term ≤ current term

## Usage

```bash
./run_tlc.sh              # Run all models (default)
./run_tlc.sh --quick      # LeaderElection + LockstepCore (~6 min)
./run_tlc.sh --full       # LockstepFull only (~10+ min)
./run_tlc.sh --force      # Ignore cache, re-run
```

## TypeScript Mapping

| TLA+ Action | TypeScript |
|-------------|------------|
| SubmitInput | `tick()` → `storeInput()` → `broadcastInput()` |
| AdvanceFrame | `tryAdvanceFrame()` |
| GenerateEvent | `eventQueue.addEvents()` |
| SendStateSync | `broadcastStateSync()` |
| ReceiveStateSync | `receiveSyncMessage()` → `eventQueue.onStateSync()` |
| BroadcastHeartbeat | `broadcastHeartbeat()` |
| StartElection | `startElection()` |
| Vote | `handleRequestVote()` |
| BecomeLeader | `becomeLeader()` |
| StepDown | `stepDown()` |

## Files

```
tla/
├── LeaderElection.tla    # Election only (5 peers)
├── MCLeaderElection.cfg
├── LockstepCore.tla      # Fast model (5 peers)
├── MCLockstepCore.cfg
├── LockstepFull.tla      # Complete model (3 peers)
├── MCLockstepFull.cfg
├── run_tlc.sh
└── .gitignore
```
