--------------------------------- MODULE LockstepNetcode ---------------------------------
\* P2P Lockstep Netcode with Leader Election and State Sync
\*
\* Models a deterministic lockstep simulation where:
\* 1. All peers must submit input before any peer advances
\* 2. Each peer advances independently (deterministic simulation ensures sync)
\* 3. Leader election uses Raft-inspired consensus
\* 4. Leader sends state syncs; followers validate by term
\*
\* This model matches the TypeScript implementation in client/src/network/

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
    /\ currentTerm[leader] > 0  \* Only send after at least one election
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
    /\ frame[candidate] >= frame[voter]
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
\* State Machine

Next ==
    \/ \E p \in Peer : SubmitInput(p)
    \/ \E p \in Peer : AdvanceFrame(p)
    \/ \E p \in Peer : GenerateEvent(p)
    \/ \E p \in Peer : SendStateSync(p)
    \/ \E f, l \in Peer : ReceiveStateSync(f, l)
    \/ \E p \in Peer : BroadcastHeartbeat(p)
    \/ \E p \in Peer : ExpireHeartbeat(p)
    \/ \E p \in Peer : StartElection(p)
    \/ \E v, c \in Peer : Vote(v, c)
    \/ \E p \in Peer : BecomeLeader(p)
    \/ \E p \in Peer : StepDown(p)
    \/ \E p \in Peer : RetryElection(p)

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

\* Frames stay within 1 of each other
FrameBoundedDrift ==
    \A i, j \in Peer : frame[i] - frame[j] <= 1 /\ frame[j] - frame[i] <= 1

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] >= 0 /\ currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : syncTerm[p] >= 0 /\ syncTerm[p] <= MaxTerm
    /\ \A p \in Peer : state[p] \in {"Leader", "Follower", "Candidate"}
    /\ \A p \in Peer : Cardinality(pendingEvents[p]) <= MaxEvents

\* Leader is at least as up-to-date as peers
LeaderUpToDate ==
    \A leader, p \in Peer : IsLeader(leader) => frame[leader] >= frame[p] - 1

\* After state sync, follower's pending events contain ONLY local events
\* This is the key property of LocalEventQueue.getEventsForReapply()
\* (Note: This is always true due to how GenerateEvent works - events are <<owner, frame>> tuples
\*  where owner is always the peer generating the event)
LocalEventsPreserved ==
    \A p \in Peer : \A e \in pendingEvents[p] : e[1] = p

----
\* Liveness

EventuallyLeader == <>(\E p \in Peer : IsLeader(p))

===============================================================================
