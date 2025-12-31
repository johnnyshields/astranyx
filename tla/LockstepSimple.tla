--------------------------------- MODULE LockstepSimple ---------------------------------
\* Simplified P2P Lockstep Netcode Model
\*
\* Fast verification model (~10M states) covering:
\* 1. Lockstep frame synchronization
\* 2. Raft-inspired leader election
\* 3. State sync with leader authority
\* 4. Owner-authoritative events (boolean)
\*
\* For detailed verification, use LockstepState.tla
\* Implementation: client/src/network/
\*
\* ============================================================================
\* SIMPLIFICATIONS vs LockstepState
\* ============================================================================
\*
\* 1. ATOMIC STATE SYNC (vs async in LockstepState)
\*    - Here: SendStateSync instantly clears all follower events
\*    - LockstepState: Separate SendStateSync + ReceiveStateSync actions
\*    - Impact: This model CANNOT catch:
\*      * Stale sync from outdated leader (no term validation)
\*      * Race conditions between send and receive
\*      * Out-of-order sync messages
\*    - Use LockstepState for realistic sync verification
\*
\* 2. BOOLEAN EVENTS (vs <<owner, frame>> tuples)
\*    - Here: hasPendingEvent is TRUE/FALSE per peer
\*    - LockstepState: pendingEvents is set of <<owner, frame>> tuples
\*    - Impact: Cannot verify LocalEventsPreserved invariant
\*
\* 3. NO TERM VALIDATION
\*    - Here: No syncTerm tracking
\*    - LockstepState: syncTerm prevents accepting stale syncs
\*
\* 4. NO DESYNC DETECTION
\*    - Here: No inSync variable or Desync action
\*    - LockstepState: Models checksum-based desync detection
\*
\* These simplifications reduce state space for fast iteration (~1M states).
\* Use LockstepState.tla for comprehensive verification (~50M states).
\* ============================================================================

EXTENDS Integers, FiniteSets

CONSTANT Peer
CONSTANT MaxFrame
CONSTANT MaxTerm

----
\* Variables (8 total - simplified from LockstepState's 10)

VARIABLE frame             \* Current frame per peer
VARIABLE inputsReceived    \* Peers who submitted input
VARIABLE currentTerm       \* Election term per peer
VARIABLE state             \* "Follower", "Candidate", "Leader"
VARIABLE votedFor          \* Vote tracking (0 = none)
VARIABLE votesReceived     \* Votes received by candidates
VARIABLE heartbeatReceived \* Heartbeat tracking
VARIABLE hasPendingEvent   \* Boolean: does peer have pending event?

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
    /\ votedFor = [p \in Peer |-> IF p = MinPeer THEN p ELSE 0]  \* Initial leader voted for self
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
\* Owner-Authoritative Events (simplified to boolean)

GenerateEvent(p) ==
    /\ ~hasPendingEvent[p]
    /\ hasPendingEvent' = [hasPendingEvent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<frame, inputsReceived, currentTerm, state, votedFor, votesReceived, heartbeatReceived>>

----
\* State Sync (atomic send+receive, leader clears follower events)

SendStateSync(leader) ==
    /\ IsLeader(leader)
    /\ hasPendingEvent' = [p \in Peer |-> IF p = leader THEN hasPendingEvent[p] ELSE FALSE]
    /\ UNCHANGED <<frame, inputsReceived, currentTerm, state, votedFor, votesReceived, heartbeatReceived>>

----
\* Leader Election

\* Note: Sets all peers' heartbeatReceived including leader (simplification - leader never checks its own)
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
    /\ frame[candidate] >= frame[voter]
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

\* Candidate must have voted for self
CandidateVotedForSelf ==
    \A p \in Peer : state[p] = "Candidate" => votedFor[p] = p

\* Leader must have voted for self
LeaderVotedForSelf ==
    \A p \in Peer : IsLeader(p) => votedFor[p] = p

\* votedFor is either 0 (none) or a valid peer
VotedForValid ==
    \A p \in Peer : votedFor[p] = 0 \/ votedFor[p] \in Peer

\* Votes received must be from valid peers
VotesFromValidPeers ==
    \A p \in Peer : votesReceived[p] \subseteq Peer

\* Leader had majority when elected
LeaderHadMajority ==
    \A p \in Peer : IsLeader(p) => IsMajority(votesReceived[p])

\* inputsReceived is a subset of Peer
InputsFromValidPeers ==
    inputsReceived \subseteq Peer

----
\* State constraint

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm

===============================================================================
