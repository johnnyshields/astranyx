--------------------------------- MODULE LeaderElection ---------------------------------
\* Raft-inspired Leader Election for P2P multiplayer
\*
\* Models the election protocol:
\* 1. Peers are Follower, Candidate, or Leader
\* 2. Leader sends heartbeats to maintain authority
\* 3. Followers become candidates on heartbeat timeout
\* 4. Candidates request votes, win with majority
\* 5. Higher terms cause stepdown
\* 6. Votes require candidate to be at least as up-to-date (frame comparison)
\*
\* Implementation: client/src/network/LeaderElection.ts

EXTENDS Integers, FiniteSets

CONSTANT Peer
CONSTANT MaxTerm
CONSTANT MaxFrame          \* For frame comparison in voting

----
\* Variables

VARIABLE currentTerm       \* Election term for each peer
VARIABLE state             \* "Follower", "Candidate", "Leader"
VARIABLE votedFor          \* Who voted for whom (0 = none)
VARIABLE votesReceived     \* Votes received by candidates
VARIABLE heartbeatReceived \* Whether heartbeat received this round
VARIABLE frame             \* Current frame per peer (for log comparison)

vars == <<currentTerm, state, votedFor, votesReceived, heartbeatReceived, frame>>

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
    /\ votedFor = [p \in Peer |-> IF p = MinPeer THEN p ELSE 0]  \* Initial leader voted for self
    /\ votesReceived = [p \in Peer |-> {}]
    /\ heartbeatReceived = [p \in Peer |-> TRUE]
    /\ frame = [p \in Peer |-> 0]

----
\* Heartbeat Actions

\* Implementation: broadcastHeartbeat()
\* Note: Sets all peers' heartbeatReceived to TRUE (leader included for simplicity)
BroadcastHeartbeat(leader) ==
    /\ IsLeader(leader)
    /\ heartbeatReceived' = [p \in Peer |-> TRUE]
    /\ UNCHANGED <<currentTerm, state, votedFor, votesReceived, frame>>

\* Implementation: election timer checks timeSinceHeartbeat >= electionTimeout
ExpireHeartbeat(p) ==
    /\ heartbeatReceived[p] = TRUE
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<currentTerm, state, votedFor, votesReceived, frame>>

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
    /\ UNCHANGED <<frame>>

\* Implementation: handleVoteRequest()
\* Key: Candidate must be at least as up-to-date as voter (frame comparison)
\* This matches LeaderElection.ts:303 - message.lastFrame >= this.currentFrame
Vote(voter, candidate) ==
    /\ state[candidate] = "Candidate"
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ frame[candidate] >= frame[voter]  \* Log comparison - candidate at least as current
    /\ \/ votedFor[voter] = 0
       \/ currentTerm[candidate] > currentTerm[voter]
    /\ votedFor' = [votedFor EXCEPT ![voter] = candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![voter] = currentTerm[candidate]]
    /\ votesReceived' = [votesReceived EXCEPT ![candidate] = votesReceived[candidate] \union {voter}]
    /\ state' = [state EXCEPT ![voter] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![voter] = TRUE]
    /\ UNCHANGED <<frame>>

\* Implementation: becomeLeader()
BecomeLeader(p) ==
    /\ state[p] = "Candidate"
    /\ IsMajority(votesReceived[p])
    /\ state' = [state EXCEPT ![p] = "Leader"]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, heartbeatReceived, frame>>

\* Implementation: stepDown()
StepDown(p) ==
    /\ IsLeader(p)
    /\ \E q \in Peer : currentTerm[q] > currentTerm[p]
    /\ state' = [state EXCEPT ![p] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frame>>

\* Implementation: election timer retry
RetryElection(p) ==
    /\ state[p] = "Candidate"
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ UNCHANGED <<state, heartbeatReceived, frame>>

\* Frame advancement (abstract - just allows frame to increase for voting comparison)
AdvanceFrame(p) ==
    /\ frame[p] < MaxFrame
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ UNCHANGED <<currentTerm, state, votedFor, votesReceived, heartbeatReceived>>

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
    \/ \E p \in Peer : AdvanceFrame(p)

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
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : state[p] \in {"Leader", "Follower", "Candidate"}

\* If candidate, must have voted for self
\* Implementation: LeaderElection.ts - startElection() sets votedFor = localPlayerId
CandidateVotedForSelf ==
    \A p \in Peer : state[p] = "Candidate" => votedFor[p] = p

\* If leader, must have voted for self (became leader via candidacy)
\* Implementation: Leader was candidate who won election after voting for self
LeaderVotedForSelf ==
    \A p \in Peer : IsLeader(p) => votedFor[p] = p

\* votedFor is either 0 (none) or a valid peer
\* Implementation: votedFor is string | null in TypeScript
VotedForValid ==
    \A p \in Peer : votedFor[p] = 0 \/ votedFor[p] \in Peer

\* Votes received must be from valid peers
VotesFromValidPeers ==
    \A p \in Peer : votesReceived[p] \subseteq Peer

\* Leader had majority when elected
LeaderHadMajority ==
    \A p \in Peer : IsLeader(p) => IsMajority(votesReceived[p])

----
\* Liveness

\* Eventually there is a leader
EventuallyLeader == <>(\E p \in Peer : IsLeader(p))

----
\* State constraint for finite model checking

StateConstraint ==
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : frame[p] <= MaxFrame

===============================================================================
