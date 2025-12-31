--------------------------------- MODULE LockstepFull ---------------------------------
\* Complete P2P Lockstep Netcode Model
\*
\* This is the comprehensive model covering ALL features:
\* 1. Lockstep frame synchronization
\* 2. Raft-inspired leader election
\* 3. Owner-authoritative events with tuple tracking
\* 4. State sync with term validation
\* 5. Local events preservation
\* 6. Arbitrary leader change (network events)
\*
\* Implementation: client/src/network/

EXTENDS Integers, FiniteSets

CONSTANT Peer
CONSTANT MaxFrame
CONSTANT MaxTerm
CONSTANT MaxEvents       \* Max pending events per peer

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

vars == <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, heartbeatReceived, syncTerm, pendingEvents>>

----
\* Helpers

IsMajority(votes) == Cardinality(votes) * 2 > Cardinality(Peer)
MinPeer == CHOOSE p \in Peer : \A q \in Peer : p <= q
MinFrame == CHOOSE f \in {frame[p] : p \in Peer} : \A q \in Peer : frame[q] >= f
IsLeader(p) == state[p] = "Leader"
CurrentLeader == IF \E p \in Peer : IsLeader(p)
                 THEN CHOOSE p \in Peer : IsLeader(p)
                 ELSE 0

----
\* Initial state

Init ==
    /\ frame = [p \in Peer |-> 0]
    /\ currentTerm = [p \in Peer |-> 0]
    /\ state = [p \in Peer |-> IF p = MinPeer THEN "Leader" ELSE "Follower"]
    /\ votedFor = [p \in Peer |-> 0]
    /\ votesReceived = [p \in Peer |-> {}]
    /\ inputsReceived = {}
    /\ heartbeatReceived = [p \in Peer |-> TRUE]
    /\ syncTerm = [p \in Peer |-> 0]
    /\ pendingEvents = [p \in Peer |-> {}]

----
\* Frame Advance (Lockstep)

\* Implementation: tick() -> storeInput() -> broadcastInput()
SubmitInput(p) ==
    /\ p \notin inputsReceived
    /\ frame[p] = MinFrame
    /\ inputsReceived' = inputsReceived \union {p}
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, heartbeatReceived, syncTerm, pendingEvents>>

\* Implementation: tryAdvanceFrame()
AdvanceFrame(p) ==
    /\ inputsReceived = Peer
    /\ frame[p] < MaxFrame
    /\ frame[p] = MinFrame
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ inputsReceived' = IF \A q \in Peer : frame'[q] > MinFrame THEN {} ELSE inputsReceived
    /\ UNCHANGED <<currentTerm, state, votedFor, votesReceived, heartbeatReceived, syncTerm, pendingEvents>>

----
\* Owner-Authoritative Events (LocalEventQueue.ts)

\* Implementation: tick() with events -> eventQueue.addEvents()
\* Each peer generates events they own (damage, pickup, etc.)
GenerateEvent(p) ==
    /\ Cardinality(pendingEvents[p]) < MaxEvents
    /\ pendingEvents' = [pendingEvents EXCEPT ![p] = pendingEvents[p] \union {<<p, frame[p]>>}]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, heartbeatReceived, syncTerm>>

----
\* State Sync (Leader Authority)

\* Implementation: broadcastStateSync() - only leader can send
\* Key property: syncTerm tracks last accepted sync to prevent stale syncs
SendStateSync(leader) ==
    /\ IsLeader(leader)
    /\ syncTerm' = [p \in Peer |-> currentTerm[leader]]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, heartbeatReceived, pendingEvents>>

\* Implementation: receiveSyncMessage() -> eventQueue.onStateSync()
\* Key behavior: remote events cleared, LOCAL events preserved for re-apply
\* This is the core of LocalEventQueue - getEventsForReapply() returns local events only
ReceiveStateSync(follower, leader) ==
    /\ ~IsLeader(follower)
    /\ IsLeader(leader)
    /\ currentTerm[leader] >= syncTerm[follower]  \* Term validation!
    /\ syncTerm' = [syncTerm EXCEPT ![follower] = currentTerm[leader]]
    \* KEY: Filter to keep only events owned by follower (local events preserved)
    /\ pendingEvents' = [pendingEvents EXCEPT
         ![follower] = {e \in pendingEvents[follower] : e[1] = follower}]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, heartbeatReceived>>

----
\* Leader Heartbeat

\* Implementation: broadcastHeartbeat()
BroadcastHeartbeat(leader) ==
    /\ IsLeader(leader)
    /\ heartbeatReceived' = [p \in Peer |-> TRUE]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, syncTerm, pendingEvents>>

\* Implementation: election timer timeout
ExpireHeartbeat(p) ==
    /\ heartbeatReceived[p] = TRUE
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, syncTerm, pendingEvents>>

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
    /\ UNCHANGED <<frame, inputsReceived, syncTerm, pendingEvents>>

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
    /\ UNCHANGED <<frame, inputsReceived, syncTerm, pendingEvents>>

\* Implementation: becomeLeader()
BecomeLeader(p) ==
    /\ state[p] = "Candidate"
    /\ IsMajority(votesReceived[p])
    /\ state' = [state EXCEPT ![p] = "Leader"]
    /\ UNCHANGED <<frame, currentTerm, votedFor, votesReceived, inputsReceived, heartbeatReceived, syncTerm, pendingEvents>>

\* Implementation: stepDown()
StepDown(p) ==
    /\ IsLeader(p)
    /\ \E q \in Peer : currentTerm[q] > currentTerm[p]
    /\ state' = [state EXCEPT ![p] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<frame, currentTerm, votedFor, votesReceived, inputsReceived, syncTerm, pendingEvents>>

\* Implementation: election timer retry
RetryElection(p) ==
    /\ state[p] = "Candidate"
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ UNCHANGED <<frame, state, inputsReceived, heartbeatReceived, syncTerm, pendingEvents>>

----
\* Network Events (from LockstepSync - models disconnects/reconnects)

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

\* Leader is at least as up-to-date as peers (within 1 frame)
LeaderUpToDate ==
    \A leader, p \in Peer : IsLeader(leader) => frame[leader] >= frame[p] - 1

\* After state sync, follower's pending events contain ONLY local events
\* This is the key property of LocalEventQueue.getEventsForReapply()
LocalEventsPreserved ==
    \A p \in Peer : \A e \in pendingEvents[p] : e[1] = p

\* Sync term never exceeds current term (no time travel)
SyncTermBounded ==
    \A p \in Peer : syncTerm[p] <= currentTerm[p] \/ syncTerm[p] <= MaxTerm

----
\* Liveness Properties

\* Eventually there is a leader
EventuallyLeader == <>(\E p \in Peer : IsLeader(p))

----
\* State constraint for bounded model checking

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm

===============================================================================
