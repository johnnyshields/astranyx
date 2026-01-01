--------------------------------- MODULE LockstepState ---------------------------------
\* Complete P2P Lockstep Netcode Model
\*
\* This is the comprehensive model covering:
\* 1. Lockstep frame synchronization
\* 2. Raft-inspired leader election
\* 3. Owner-authoritative events with tuple tracking
\* 4. State sync with term validation
\* 5. Local events preservation
\* 6. Arbitrary leader change (network events)
\* 7. Checksum-based desync detection and recovery
\*
\* Implementation: client/src/network/
\*
\* ============================================================================
\* MODELING LIMITATIONS (intentional simplifications)
\* ============================================================================
\*
\* NOT MODELED (covered by Jepsen tests instead):
\* - Message loss/reordering: Messages are delivered atomically
\* - Peer connect/disconnect: Peer set is static
\* - Real timing: Timeouts are boolean, not timestamps
\* - InputBuffer per-frame storage: Single inputsReceived set
\* - WebRTC connection states: No connection abstraction
\*
\* These simplifications keep state space manageable (~50M states)
\* while still verifying core safety properties.
\* ============================================================================

EXTENDS Integers, FiniteSets

CONSTANT Peer
CONSTANT MaxFrame
CONSTANT MaxTerm
CONSTANT MaxEvents       \* Max pending events per peer
CONSTANT InitialLeader   \* First peer to be leader (typically the host)

----
\* Variables

VARIABLE frame           \* Current simulation frame for each peer
VARIABLE currentTerm     \* Election term for each peer
VARIABLE state           \* "Follower", "Candidate", "Leader"
VARIABLE votedFor        \* Who this peer voted for (0 = none)
VARIABLE votesReceived   \* Votes received by each peer
VARIABLE inputsReceived  \* Peers who submitted input for current frame
VARIABLE heartbeatReceived \* Whether heartbeat received this round
VARIABLE syncTerm        \* Term of last accepted state sync (for validation)
VARIABLE pendingEvents   \* Pending events per peer: set of <<owner, frame>> tuples
VARIABLE inSync          \* Whether peer's state matches leader (checksum abstraction)

vars == <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, heartbeatReceived, syncTerm, pendingEvents, inSync>>

----
\* Helpers

IsMajority(votes) == Cardinality(votes) * 2 > Cardinality(Peer)
MinFrame == CHOOSE f \in {frame[p] : p \in Peer} : \A q \in Peer : frame[q] >= f
IsLeader(p) == state[p] = "Leader"

----
\* Initial state - InitialLeader starts as leader, others as followers

Init ==
    /\ frame = [p \in Peer |-> 0]
    /\ currentTerm = [p \in Peer |-> 0]
    /\ state = [p \in Peer |-> IF p = InitialLeader THEN "Leader" ELSE "Follower"]
    /\ votedFor = [p \in Peer |-> IF p = InitialLeader THEN p ELSE 0]
    /\ votesReceived = [p \in Peer |-> {}]
    /\ inputsReceived = {}
    /\ heartbeatReceived = [p \in Peer |-> TRUE]
    /\ syncTerm = [p \in Peer |-> 0]
    /\ pendingEvents = [p \in Peer |-> {}]
    /\ inSync = [p \in Peer |-> TRUE]  \* Initially all in sync

----
\* Frame Advance (Lockstep)

\* Implementation: tick() -> storeInput() -> broadcastInput()
SubmitInput(p) ==
    /\ p \notin inputsReceived
    /\ frame[p] = MinFrame
    /\ inputsReceived' = inputsReceived \union {p}
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, heartbeatReceived, syncTerm, pendingEvents, inSync>>

\* Implementation: tryAdvanceFrame()
AdvanceFrame(p) ==
    /\ inputsReceived = Peer
    /\ frame[p] < MaxFrame
    /\ frame[p] = MinFrame
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ inputsReceived' = IF \A q \in Peer : frame'[q] > MinFrame THEN {} ELSE inputsReceived
    /\ UNCHANGED <<currentTerm, state, votedFor, votesReceived, heartbeatReceived, syncTerm, pendingEvents, inSync>>

----
\* Owner-Authoritative Events (LocalEventQueue.ts)

\* Implementation: tick() with events -> eventQueue.addEvents()
\* Each peer generates events they own (damage, pickup, etc.)
GenerateEvent(p) ==
    /\ Cardinality(pendingEvents[p]) < MaxEvents
    /\ pendingEvents' = [pendingEvents EXCEPT ![p] = pendingEvents[p] \union {<<p, frame[p]>>}]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, heartbeatReceived, syncTerm, inSync>>

----
\* State Sync (Leader Authority)
\*
\* CONCURRENT SYNC HANDLING:
\* - SendStateSync broadcasts to all peers (marks sync pending)
\* - ReceiveStateSync processes per-follower (validates term)
\* - Term validation (syncTerm) handles:
\*   * Stale syncs from old leaders (rejected)
\*   * Out-of-order sync messages (older term rejected)
\*   * Concurrent syncs from same leader (idempotent)
\*
\* The syncTerm variable acts as a logical clock ensuring
\* followers only accept syncs from current or higher terms.

\* Implementation: broadcastStateSync() - only leader can send
\* Key property: syncTerm tracks last accepted sync to prevent stale syncs
\* Leader updates its own syncTerm; followers update theirs in ReceiveStateSync
SendStateSync(leader) ==
    /\ IsLeader(leader)
    /\ syncTerm' = [syncTerm EXCEPT ![leader] = currentTerm[leader]]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, heartbeatReceived, pendingEvents, inSync>>

\* Implementation: receiveSyncMessage() -> eventQueue.onStateSync()
\* Key behavior: remote events cleared, LOCAL events preserved for re-apply
\* This is the core of LocalEventQueue - getEventsForReapply() returns local events only
\* Also resets inSync to TRUE (follower now matches leader state)
\*
\* CONCURRENT SYNC SAFETY:
\* - Term validation ensures only current/higher term syncs accepted
\* - Multiple concurrent syncs from same term are idempotent
\* - Stale syncs (lower term) are silently rejected
\*
\* RAFT RULE: Any message from higher term causes step down to follower.
\* This applies to candidates too - if a candidate receives a state sync from
\* a leader with higher term, they must abandon their election.
\* This prevents stale candidates from using old votes after term bump.
ReceiveStateSync(follower, leader) ==
    /\ ~IsLeader(follower)
    /\ IsLeader(leader)
    /\ currentTerm[leader] >= syncTerm[follower]  \* Term validation!
    /\ currentTerm' = [currentTerm EXCEPT ![follower] = IF currentTerm[leader] > currentTerm[follower] THEN currentTerm[leader] ELSE currentTerm[follower]]
    /\ syncTerm' = [syncTerm EXCEPT ![follower] = currentTerm[leader]]
    \* RAFT: Step down to follower on higher term (critical for candidates!)
    /\ state' = [state EXCEPT ![follower] = "Follower"]
    \* Clear votes - cannot use old votes in new term
    /\ votesReceived' = [votesReceived EXCEPT ![follower] = {}]
    \* Reset votedFor on term change (can vote again in new term)
    /\ votedFor' = [votedFor EXCEPT ![follower] = IF currentTerm[leader] > currentTerm[follower] THEN 0 ELSE votedFor[follower]]
    \* KEY: Filter to keep only events owned by follower (local events preserved)
    /\ pendingEvents' = [pendingEvents EXCEPT
         ![follower] = {e \in pendingEvents[follower] : e[1] = follower}]
    /\ inSync' = [inSync EXCEPT ![follower] = TRUE]  \* Sync restores consistency
    /\ UNCHANGED <<frame, inputsReceived, heartbeatReceived>>

\* Implementation: checkForDesync() detects checksum mismatch
\* Models non-deterministic state divergence (floating point drift, race conditions, etc.)
\* This triggers the need for state sync
Desync(p) ==
    /\ ~IsLeader(p)  \* Only followers can desync from leader
    /\ inSync[p] = TRUE  \* Can only desync if currently in sync
    /\ inSync' = [inSync EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, heartbeatReceived, syncTerm, pendingEvents>>

----
\* Leader Heartbeat

\* Implementation: broadcastHeartbeat()
\* Note: Sets all peers' heartbeatReceived including leader (simplification - leader never checks its own)
BroadcastHeartbeat(leader) ==
    /\ IsLeader(leader)
    /\ heartbeatReceived' = [p \in Peer |-> TRUE]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, syncTerm, pendingEvents, inSync>>

\* Implementation: election timer timeout
ExpireHeartbeat(p) ==
    /\ heartbeatReceived[p] = TRUE
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, syncTerm, pendingEvents, inSync>>

----
\* Election

\* Implementation: startElection()
StartElection(p) ==
    /\ state[p] = "Follower"
    /\ heartbeatReceived[p] = FALSE
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ state' = [state EXCEPT ![p] = "Candidate"]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<frame, inputsReceived, syncTerm, pendingEvents, inSync>>

\* Implementation: handleVoteRequest()
Vote(voter, candidate) ==
    /\ state[candidate] = "Candidate"
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ frame[candidate] >= frame[voter]  \* Log comparison (frame = log index)
    /\ \/ votedFor[voter] = 0
       \/ currentTerm[candidate] > currentTerm[voter]
    /\ votedFor' = [votedFor EXCEPT ![voter] = candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![voter] = currentTerm[candidate]]
    /\ votesReceived' = [votesReceived EXCEPT ![candidate] = votesReceived[candidate] \union {voter}]
    /\ state' = [state EXCEPT ![voter] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![voter] = TRUE]
    /\ UNCHANGED <<frame, inputsReceived, syncTerm, pendingEvents, inSync>>

\* Implementation: becomeLeader()
BecomeLeader(p) ==
    /\ state[p] = "Candidate"
    /\ IsMajority(votesReceived[p])
    /\ state' = [state EXCEPT ![p] = "Leader"]
    /\ UNCHANGED <<frame, currentTerm, votedFor, votesReceived, inputsReceived, heartbeatReceived, syncTerm, pendingEvents, inSync>>

\* Implementation: stepDown()
StepDown(p) ==
    /\ IsLeader(p)
    /\ \E q \in Peer : currentTerm[q] > currentTerm[p]
    /\ state' = [state EXCEPT ![p] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<frame, currentTerm, votedFor, votesReceived, inputsReceived, syncTerm, pendingEvents, inSync>>

\* Implementation: election timer retry
RetryElection(p) ==
    /\ state[p] = "Candidate"
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ UNCHANGED <<frame, state, inputsReceived, heartbeatReceived, syncTerm, pendingEvents, inSync>>

----
\* Network Events (from LockstepNetwork - models disconnects/reconnects)

\* Models arbitrary leadership change due to network events
\* (peer disconnect, network partition, manual override)
MaxCurrentTerm == CHOOSE t \in {currentTerm[p] : p \in Peer} : \A q \in Peer : currentTerm[q] <= t

ForceLeaderChange(oldLeader, newLeader) ==
    /\ oldLeader # newLeader
    /\ IsLeader(oldLeader)
    /\ ~IsLeader(newLeader)  \* Can't force someone who's already leader
    /\ MaxCurrentTerm < MaxTerm  \* Must have room to bump term
    /\ frame[newLeader] >= frame[oldLeader] - 1  \* New leader must be reasonably up-to-date
    \* Step down ALL other leaders and make newLeader the sole leader
    /\ state' = [p \in Peer |-> IF p = newLeader THEN "Leader" ELSE "Follower"]
    /\ currentTerm' = [p \in Peer |-> MaxCurrentTerm + 1]  \* Bump everyone to same term
    /\ votedFor' = [p \in Peer |-> newLeader]  \* Everyone "voted" for new leader
    /\ votesReceived' = [votesReceived EXCEPT ![newLeader] = Peer]
    /\ heartbeatReceived' = [p \in Peer |-> TRUE]
    \* After leader change, followers may be out of sync with new leader
    /\ inSync' = [p \in Peer |-> p = newLeader]  \* Only new leader is "in sync" with itself
    /\ UNCHANGED <<frame, inputsReceived, syncTerm, pendingEvents>>

----
\* State Machine

Next ==
    \* Lockstep
    \/ \E p \in Peer : SubmitInput(p)
    \/ \E p \in Peer : AdvanceFrame(p)
    \* Events
    \/ \E p \in Peer : GenerateEvent(p)
    \* State Sync
    \/ \E p \in Peer : SendStateSync(p)
    \/ \E f, l \in Peer : ReceiveStateSync(f, l)
    \* Desync (models checksum mismatch detection)
    \/ \E p \in Peer : Desync(p)
    \* Heartbeat
    \/ \E p \in Peer : BroadcastHeartbeat(p)
    \/ \E p \in Peer : ExpireHeartbeat(p)
    \* Election
    \/ \E p \in Peer : StartElection(p)
    \/ \E v, c \in Peer : Vote(v, c)
    \/ \E p \in Peer : BecomeLeader(p)
    \/ \E p \in Peer : StepDown(p)
    \/ \E p \in Peer : RetryElection(p)
    \* Network Events
    \/ \E old, new \in Peer : ForceLeaderChange(old, new)

Fairness ==
    /\ WF_vars(\E p \in Peer : SubmitInput(p))
    /\ WF_vars(\E p \in Peer : AdvanceFrame(p))
    /\ WF_vars(\E p \in Peer : BroadcastHeartbeat(p))
    /\ WF_vars(\E p \in Peer : BecomeLeader(p))
    /\ WF_vars(\E f, l \in Peer : ReceiveStateSync(f, l))  \* Desync eventually corrected

Spec == Init /\ [][Next]_vars /\ Fairness

----
\* Safety Properties

\* No two leaders in same term
NoTwoLeadersInSameTerm ==
    \A i, j \in Peer :
        (i # j /\ IsLeader(i) /\ IsLeader(j)) => currentTerm[i] # currentTerm[j]

\* Frames stay within 1 of each other (lockstep guarantee)
FrameBoundedDrift ==
    \A i, j \in Peer : frame[i] - frame[j] <= 1 /\ frame[j] - frame[i] <= 1

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] >= 0 /\ currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : syncTerm[p] >= 0 /\ syncTerm[p] <= MaxTerm
    /\ \A p \in Peer : state[p] \in {"Leader", "Follower", "Candidate"}
    /\ \A p \in Peer : Cardinality(pendingEvents[p]) <= MaxEvents
    /\ \A p \in Peer : inSync[p] \in BOOLEAN

\* Leader is at least as up-to-date as peers (within 1 frame)
LeaderUpToDate ==
    \A leader, p \in Peer : IsLeader(leader) => frame[leader] >= frame[p] - 1

\* After state sync, follower's pending events contain ONLY local events
LocalEventsPreserved ==
    \A p \in Peer : \A e \in pendingEvents[p] : e[1] = p

\* Sync term never exceeds current term (no time travel)
SyncTermBounded ==
    \A p \in Peer : syncTerm[p] <= currentTerm[p]

\* Candidate must have voted for self
CandidateVotedForSelf ==
    \A p \in Peer : state[p] = "Candidate" => votedFor[p] = p

\* Leader must have voted for self
LeaderVotedForSelf ==
    \A p \in Peer : IsLeader(p) => votedFor[p] = p

\* Leader had majority when elected (or initial/forced leader)
LeaderHadMajority ==
    \A p \in Peer : IsLeader(p) =>
        \/ IsMajority(votesReceived[p])
        \/ currentTerm[p] = 0         \* Initial leader assigned without election
        \/ votesReceived[p] = Peer    \* ForceLeaderChange gives all votes

\* Votes received must be from valid peers
VotesFromValidPeers ==
    \A p \in Peer : votesReceived[p] \subseteq Peer

\* votedFor must be 0 (none) or a valid peer
VotedForValid ==
    \A p \in Peer : votedFor[p] = 0 \/ votedFor[p] \in Peer

\* inputsReceived is a subset of Peer
InputsFromValidPeers ==
    inputsReceived \subseteq Peer

----
\* Liveness Properties

\* Eventually there is a leader
EventuallyLeader == <>(\E p \in Peer : IsLeader(p))

\* If there's a leader, desync is eventually corrected
\* (state sync will bring followers back in sync)
DesyncEventuallyCorrected ==
    (\E p \in Peer : IsLeader(p)) => <>(\A p \in Peer : inSync[p])

----
\* State constraint for bounded model checking

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm

===============================================================================
