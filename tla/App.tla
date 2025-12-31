--------------------------------- MODULE App ---------------------------------
\* Combined P2P Lockstep Netcode Model
\*
\* Simplified model covering:
\* 1. Leader election (Raft-inspired)
\* 2. Lockstep frame synchronization
\* 3. State sync with leader authority
\* 4. Owner-authoritative events
\*
\* This is the integration model - verifies the components work together.
\* Implementation: client/src/network/

EXTENDS Integers, FiniteSets

CONSTANT Peer
CONSTANT MaxFrame
CONSTANT MaxTerm

----
\* Variables

VARIABLE frame             \* Current frame per peer
VARIABLE inputsReceived    \* Peers who submitted input
VARIABLE currentTerm       \* Election term per peer
VARIABLE state             \* "Follower", "Candidate", "Leader"
VARIABLE votedFor          \* Vote tracking
VARIABLE votesReceived     \* Votes received
VARIABLE heartbeatReceived \* Heartbeat tracking
VARIABLE hasPendingEvent   \* Does peer have pending local event?

vars == <<frame, inputsReceived, currentTerm, state, votedFor, votesReceived, heartbeatReceived, hasPendingEvent>>

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
    /\ inputsReceived = {}
    /\ currentTerm = [p \in Peer |-> 0]
    /\ state = [p \in Peer |-> IF p = MinPeer THEN "Leader" ELSE "Follower"]
    /\ votedFor = [p \in Peer |-> 0]
    /\ votesReceived = [p \in Peer |-> {}]
    /\ heartbeatReceived = [p \in Peer |-> TRUE]
    /\ hasPendingEvent = [p \in Peer |-> FALSE]

----
\* Lockstep Frame Advance

SubmitInput(p) ==
    /\ p \notin inputsReceived
    /\ frame[p] = MinFrame
    /\ inputsReceived' = inputsReceived \union {p}
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, heartbeatReceived, hasPendingEvent>>

AdvanceFrame(p) ==
    /\ inputsReceived = Peer
    /\ frame[p] < MaxFrame
    /\ frame[p] = MinFrame
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ inputsReceived' = IF \A q \in Peer : frame'[q] > MinFrame THEN {} ELSE inputsReceived
    /\ UNCHANGED <<currentTerm, state, votedFor, votesReceived, heartbeatReceived, hasPendingEvent>>

----
\* Owner-Authoritative Events

GenerateEvent(p) ==
    /\ ~hasPendingEvent[p]
    /\ hasPendingEvent' = [hasPendingEvent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<frame, inputsReceived, currentTerm, state, votedFor, votesReceived, heartbeatReceived>>

----
\* State Sync (requires leader)

SendStateSync(leader) ==
    /\ IsLeader(leader)
    /\ hasPendingEvent' = [p \in Peer |-> IF p = leader THEN hasPendingEvent[p] ELSE FALSE]
    /\ UNCHANGED <<frame, inputsReceived, currentTerm, state, votedFor, votesReceived, heartbeatReceived>>

----
\* Leader Election

BroadcastHeartbeat(leader) ==
    /\ IsLeader(leader)
    /\ heartbeatReceived' = [p \in Peer |-> TRUE]
    /\ UNCHANGED <<frame, inputsReceived, currentTerm, state, votedFor, votesReceived, hasPendingEvent>>

ExpireHeartbeat(p) ==
    /\ heartbeatReceived[p] = TRUE
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<frame, inputsReceived, currentTerm, state, votedFor, votesReceived, hasPendingEvent>>

StartElection(p) ==
    /\ state[p] = "Follower"
    /\ heartbeatReceived[p] = FALSE
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ state' = [state EXCEPT ![p] = "Candidate"]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<frame, inputsReceived, hasPendingEvent>>

Vote(voter, candidate) ==
    /\ state[candidate] = "Candidate"
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ frame[candidate] >= frame[voter]  \* Log comparison
    /\ \/ votedFor[voter] = 0
       \/ currentTerm[candidate] > currentTerm[voter]
    /\ votedFor' = [votedFor EXCEPT ![voter] = candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![voter] = currentTerm[candidate]]
    /\ votesReceived' = [votesReceived EXCEPT ![candidate] = votesReceived[candidate] \union {voter}]
    /\ state' = [state EXCEPT ![voter] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![voter] = TRUE]
    /\ UNCHANGED <<frame, inputsReceived, hasPendingEvent>>

BecomeLeader(p) ==
    /\ state[p] = "Candidate"
    /\ IsMajority(votesReceived[p])
    /\ state' = [state EXCEPT ![p] = "Leader"]
    /\ UNCHANGED <<frame, inputsReceived, currentTerm, votedFor, votesReceived, heartbeatReceived, hasPendingEvent>>

StepDown(p) ==
    /\ IsLeader(p)
    /\ \E q \in Peer : currentTerm[q] > currentTerm[p]
    /\ state' = [state EXCEPT ![p] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<frame, inputsReceived, currentTerm, votedFor, votesReceived, hasPendingEvent>>

RetryElection(p) ==
    /\ state[p] = "Candidate"
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ UNCHANGED <<frame, inputsReceived, state, heartbeatReceived, hasPendingEvent>>

----
\* State Machine

Next ==
    \/ \E p \in Peer : SubmitInput(p)
    \/ \E p \in Peer : AdvanceFrame(p)
    \/ \E p \in Peer : GenerateEvent(p)
    \/ \E p \in Peer : SendStateSync(p)
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

NoTwoLeadersInSameTerm ==
    \A i, j \in Peer :
        (i # j /\ IsLeader(i) /\ IsLeader(j)) => currentTerm[i] # currentTerm[j]

FrameBoundedDrift ==
    \A i, j \in Peer : frame[i] - frame[j] <= 1 /\ frame[j] - frame[i] <= 1

TypeInvariant ==
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] >= 0 /\ currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : state[p] \in {"Leader", "Follower", "Candidate"}
    /\ \A p \in Peer : hasPendingEvent[p] \in BOOLEAN

LeaderUpToDate ==
    \A leader, p \in Peer : IsLeader(leader) => frame[leader] >= frame[p] - 1

----
\* State constraint

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm

===============================================================================
