--------------------------------- MODULE LockstepSync ---------------------------------
\* Lockstep Frame Synchronization with State Sync and Events
\*
\* Models:
\* 1. All peers submit input before frame advances (lockstep)
\* 2. Peers generate owner-authoritative events
\* 3. Leader sends state syncs; followers preserve local events
\*
\* Implementation: LockstepNetcode.ts, StateSyncManager.ts, LocalEventQueue.ts

EXTENDS Integers, FiniteSets

CONSTANT Peer
CONSTANT MaxFrame

----
\* Variables

VARIABLE frame           \* Current frame for each peer
VARIABLE inputsReceived  \* Peers who submitted input for current frame
VARIABLE leader          \* Current leader peer
VARIABLE hasPendingEvent \* Boolean: does peer have a pending local event?

vars == <<frame, inputsReceived, leader, hasPendingEvent>>

----
\* Helpers

MinPeer == CHOOSE p \in Peer : \A q \in Peer : p <= q
MinFrame == CHOOSE f \in {frame[p] : p \in Peer} : \A q \in Peer : frame[q] >= f
IsLeader(p) == leader = p

----
\* Initial state

Init ==
    /\ frame = [p \in Peer |-> 0]
    /\ inputsReceived = {}
    /\ leader = MinPeer
    /\ hasPendingEvent = [p \in Peer |-> FALSE]

----
\* Lockstep Frame Advance

\* Implementation: tick() -> storeInput() -> broadcastInput()
SubmitInput(p) ==
    /\ p \notin inputsReceived
    /\ frame[p] = MinFrame
    /\ inputsReceived' = inputsReceived \union {p}
    /\ UNCHANGED <<frame, leader, hasPendingEvent>>

\* Implementation: tryAdvanceFrame()
AdvanceFrame(p) ==
    /\ inputsReceived = Peer
    /\ frame[p] < MaxFrame
    /\ frame[p] = MinFrame
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ inputsReceived' = IF \A q \in Peer : frame'[q] > MinFrame THEN {} ELSE inputsReceived
    /\ UNCHANGED <<leader, hasPendingEvent>>

----
\* Owner-Authoritative Events (simplified to boolean)

\* Implementation: tick() with events -> eventQueue.addEvents()
GenerateEvent(p) ==
    /\ ~hasPendingEvent[p]
    /\ hasPendingEvent' = [hasPendingEvent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<frame, inputsReceived, leader>>

----
\* State Sync (simplified - no term tracking)

\* Implementation: broadcastStateSync() - leader sends authoritative state
\* After sync, followers clear their pending events (but keep local ones)
SendStateSync(leaderPeer) ==
    /\ IsLeader(leaderPeer)
    \* Followers lose pending events (synced to leader's state)
    \* But in real impl, LOCAL events are preserved - modeled by not clearing leader's
    /\ hasPendingEvent' = [p \in Peer |-> IF p = leaderPeer THEN hasPendingEvent[p] ELSE FALSE]
    /\ UNCHANGED <<frame, inputsReceived, leader>>

\* Implementation: receiveSyncMessage() -> eventQueue.onStateSync()
\* This is implicitly handled by SendStateSync above
\* Local events preserved = leader keeps their events, followers clear

----
\* Leader Change (simplified)

ChangeLeader(newLeader) ==
    /\ newLeader \in Peer
    /\ newLeader # leader
    /\ leader' = newLeader
    /\ UNCHANGED <<frame, inputsReceived, hasPendingEvent>>

----
\* State Machine

Next ==
    \/ \E p \in Peer : SubmitInput(p)
    \/ \E p \in Peer : AdvanceFrame(p)
    \/ \E p \in Peer : GenerateEvent(p)
    \/ \E p \in Peer : SendStateSync(p)
    \/ \E p \in Peer : ChangeLeader(p)

Fairness ==
    /\ WF_vars(\E p \in Peer : SubmitInput(p))
    /\ WF_vars(\E p \in Peer : AdvanceFrame(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----
\* Safety Properties

\* Frames stay within 1 of each other (lockstep)
FrameBoundedDrift ==
    \A i, j \in Peer : frame[i] - frame[j] <= 1 /\ frame[j] - frame[i] <= 1

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ leader \in Peer
    /\ \A p \in Peer : hasPendingEvent[p] \in BOOLEAN

----
\* State constraint

StateConstraint == \A p \in Peer : frame[p] <= MaxFrame

===============================================================================
