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

\* The set of peer IDs
CONSTANT Peer

\* Model bounds
CONSTANT MaxTerm
CONSTANT MaxFrame

\* First peer to be leader (typically the host)
CONSTANT InitialLeader

(**************************************************************************************************)
(* Per-peer variables                                                                             *)
(**************************************************************************************************)

\* The peer's current election term
VARIABLE currentTerm

\* The peer's state: "Follower", "Candidate", or "Leader"
VARIABLE state

\* Who this peer voted for in current term (0 = none)
VARIABLE votedFor

\* Votes received by this peer (when candidate)
VARIABLE votesReceived

electionVars == <<currentTerm, state, votedFor, votesReceived>>

\* Whether heartbeat was received this round
VARIABLE heartbeatReceived

\* Current simulation frame (for log comparison in voting)
VARIABLE frame

frameVars == <<heartbeatReceived, frame>>

\* All variables
vars == <<electionVars, frameVars>>

----
(**************************************************************************************************)
(* Helper operators                                                                               *)
(**************************************************************************************************)

IsMajority(votes) == Cardinality(votes) * 2 > Cardinality(Peer)
IsLeader(p) == state[p] = "Leader"

----
(**************************************************************************************************)
(* Initial state                                                                                  *)
(**************************************************************************************************)

Init ==
    /\ currentTerm = [p \in Peer |-> 0]
    /\ state = [p \in Peer |-> IF p = InitialLeader THEN "Leader" ELSE "Follower"]
    /\ votedFor = [p \in Peer |-> IF p = InitialLeader THEN p ELSE 0]
    /\ votesReceived = [p \in Peer |-> {}]
    /\ heartbeatReceived = [p \in Peer |-> TRUE]
    /\ frame = [p \in Peer |-> 0]

----
(**************************************************************************************************)
(* Heartbeat actions                                                                              *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Leader broadcasts heartbeat to all peers.                                  *)
(* Implementation: broadcastHeartbeat()                                       *)
(******************************************************************************)
BroadcastHeartbeat(leader) ==
    /\ IsLeader(leader)
    /\ heartbeatReceived' = [p \in Peer |-> TRUE]
    /\ UNCHANGED <<electionVars, frame>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer's heartbeat timer expires (models timeout).                           *)
(* Implementation: election timer checks timeSinceHeartbeat >= electionTimeout*)
(******************************************************************************)
ExpireHeartbeat(p) ==
    /\ heartbeatReceived[p] = TRUE
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<electionVars, frame>>

----
(**************************************************************************************************)
(* Election actions                                                                               *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Follower starts election after heartbeat timeout.                          *)
(* Implementation: startElection()                                            *)
(******************************************************************************)
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

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Voter grants vote to candidate.                                            *)
(* Key: Candidate must be at least as up-to-date (frame comparison).          *)
(* Implementation: handleVoteRequest()                                        *)
(******************************************************************************)
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

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Candidate wins election with majority votes.                               *)
(* Implementation: becomeLeader()                                             *)
(******************************************************************************)
BecomeLeader(p) ==
    /\ state[p] = "Candidate"
    /\ IsMajority(votesReceived[p])
    /\ state' = [state EXCEPT ![p] = "Leader"]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frameVars>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Leader steps down upon seeing higher term.                                 *)
(* Implementation: stepDown()                                                 *)
(******************************************************************************)
StepDown(p) ==
    /\ IsLeader(p)
    /\ \E q \in Peer : currentTerm[q] > currentTerm[p]
    /\ state' = [state EXCEPT ![p] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frame>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Candidate retries election after timeout.                                  *)
(* Implementation: election timer retry                                       *)
(******************************************************************************)
RetryElection(p) ==
    /\ state[p] = "Candidate"
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ UNCHANGED <<state, frameVars>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer advances frame (abstract simulation progress).                        *)
(******************************************************************************)
AdvanceFrame(p) ==
    /\ frame[p] < MaxFrame
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ UNCHANGED <<electionVars, heartbeatReceived>>

----
(**************************************************************************************************)
(* Specification                                                                                  *)
(**************************************************************************************************)

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
(**************************************************************************************************)
(* Safety invariants                                                                              *)
(**************************************************************************************************)

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
CandidateVotedForSelf ==
    \A p \in Peer : state[p] = "Candidate" => votedFor[p] = p

\* If leader, must have voted for self (became leader via candidacy)
LeaderVotedForSelf ==
    \A p \in Peer : IsLeader(p) => votedFor[p] = p

\* votedFor is either 0 (none) or a valid peer
VotedForValid ==
    \A p \in Peer : votedFor[p] = 0 \/ votedFor[p] \in Peer

\* Votes received must be from valid peers
VotesFromValidPeers ==
    \A p \in Peer : votesReceived[p] \subseteq Peer

\* Leader had majority when elected (or is initial leader at term 0)
LeaderHadMajority ==
    \A p \in Peer : IsLeader(p) =>
        \/ IsMajority(votesReceived[p])
        \/ currentTerm[p] = 0  \* Initial leader assigned without election

----
(**************************************************************************************************)
(* Liveness properties                                                                            *)
(**************************************************************************************************)

\* Eventually there is a leader
EventuallyLeader == <>(\E p \in Peer : IsLeader(p))

----
(**************************************************************************************************)
(* State constraint for finite model checking                                                     *)
(**************************************************************************************************)

StateConstraint ==
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : frame[p] <= MaxFrame

===============================================================================
