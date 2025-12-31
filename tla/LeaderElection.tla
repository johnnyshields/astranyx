--------------------------------- MODULE LeaderElection ---------------------------------
\* Raft-inspired Leader Election for P2P multiplayer
\*
\* Models the election protocol:
\* 1. Peers are Follower, Candidate, or Leader
\* 2. Leader sends heartbeats to maintain authority
\* 3. Followers become candidates on heartbeat timeout
\* 4. Candidates request votes, win with majority
\* 5. Higher terms cause stepdown
\*
\* Implementation: client/src/network/LeaderElection.ts

EXTENDS Integers, FiniteSets

CONSTANT Peer
CONSTANT MaxTerm

----
\* Variables

VARIABLE currentTerm       \* Election term for each peer
VARIABLE state             \* "Follower", "Candidate", "Leader"
VARIABLE votedFor          \* Who voted for whom (0 = none)
VARIABLE votesReceived     \* Votes received by candidates
VARIABLE heartbeatReceived \* Whether heartbeat received this round

vars == <<currentTerm, state, votedFor, votesReceived, heartbeatReceived>>

----
\* Helpers

IsMajority(votes) == Cardinality(votes) * 2 > Cardinality(Peer)
MinPeer == CHOOSE p \in Peer : \A q \in Peer : p <= q
IsLeader(p) == state[p] = "Leader"

----
\* Initial state - peer with lowest ID starts as leader

Init ==
    /\ currentTerm = [p \in Peer |-> 0]
    /\ state = [p \in Peer |-> IF p = MinPeer THEN "Leader" ELSE "Follower"]
    /\ votedFor = [p \in Peer |-> 0]
    /\ votesReceived = [p \in Peer |-> {}]
    /\ heartbeatReceived = [p \in Peer |-> TRUE]

----
\* Heartbeat Actions

\* Implementation: broadcastHeartbeat()
BroadcastHeartbeat(leader) ==
    /\ IsLeader(leader)
    /\ heartbeatReceived' = [p \in Peer |-> TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, votesReceived>>

\* Implementation: election timer checks timeSinceHeartbeat >= electionTimeout
ExpireHeartbeat(p) ==
    /\ heartbeatReceived[p] = TRUE
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<currentTerm, state, votedFor, votesReceived>>

----
\* Election Actions

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

\* Implementation: handleVoteRequest()
Vote(voter, candidate) ==
    /\ state[candidate] = "Candidate"
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ \/ votedFor[voter] = 0
       \/ currentTerm[candidate] > currentTerm[voter]
    /\ votedFor' = [votedFor EXCEPT ![voter] = candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![voter] = currentTerm[candidate]]
    /\ votesReceived' = [votesReceived EXCEPT ![candidate] = votesReceived[candidate] \union {voter}]
    /\ state' = [state EXCEPT ![voter] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![voter] = TRUE]

\* Implementation: becomeLeader()
BecomeLeader(p) ==
    /\ state[p] = "Candidate"
    /\ IsMajority(votesReceived[p])
    /\ state' = [state EXCEPT ![p] = "Leader"]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, heartbeatReceived>>

\* Implementation: stepDown()
StepDown(p) ==
    /\ IsLeader(p)
    /\ \E q \in Peer : currentTerm[q] > currentTerm[p]
    /\ state' = [state EXCEPT ![p] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived>>

\* Implementation: election timer retry
RetryElection(p) ==
    /\ state[p] = "Candidate"
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ UNCHANGED <<state, heartbeatReceived>>

----
\* State Machine

Next ==
    \/ \E p \in Peer : BroadcastHeartbeat(p)
    \/ \E p \in Peer : ExpireHeartbeat(p)
    \/ \E p \in Peer : StartElection(p)
    \/ \E v, c \in Peer : Vote(v, c)
    \/ \E p \in Peer : BecomeLeader(p)
    \/ \E p \in Peer : StepDown(p)
    \/ \E p \in Peer : RetryElection(p)

Fairness ==
    /\ WF_vars(\E p \in Peer : BroadcastHeartbeat(p))
    /\ WF_vars(\E p \in Peer : BecomeLeader(p))
    /\ WF_vars(\E p \in Peer : RetryElection(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----
\* Safety Properties

\* No two leaders in same term (election safety)
NoTwoLeadersInSameTerm ==
    \A i, j \in Peer :
        (i # j /\ IsLeader(i) /\ IsLeader(j)) => currentTerm[i] # currentTerm[j]

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : currentTerm[p] >= 0 /\ currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : state[p] \in {"Leader", "Follower", "Candidate"}

----
\* Liveness

\* Eventually there is a leader
EventuallyLeader == <>(\E p \in Peer : IsLeader(p))

----
\* State constraint for finite model checking

StateConstraint == \A p \in Peer : currentTerm[p] <= MaxTerm

===============================================================================
