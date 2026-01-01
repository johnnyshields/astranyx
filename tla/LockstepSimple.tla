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

\* The set of peer IDs
CONSTANT Peer

\* Model bounds
CONSTANT MaxFrame
CONSTANT MaxTerm

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

\* Current simulation frame per peer
VARIABLE frame

\* Whether heartbeat was received this round
VARIABLE heartbeatReceived

\* Boolean: does peer have pending event?
VARIABLE hasPendingEvent

frameVars == <<frame, heartbeatReceived, hasPendingEvent>>

(**************************************************************************************************)
(* Global variables                                                                               *)
(**************************************************************************************************)

\* Peers who submitted input for current frame
VARIABLE inputsReceived

\* All variables
vars == <<electionVars, frameVars, inputsReceived>>

----
(**************************************************************************************************)
(* Helper operators                                                                               *)
(**************************************************************************************************)

IsMajority(votes) == Cardinality(votes) * 2 > Cardinality(Peer)
MinFrame == CHOOSE f \in {frame[p] : p \in Peer} : \A q \in Peer : frame[q] >= f
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
    /\ frame = [p \in Peer |-> 0]
    /\ heartbeatReceived = [p \in Peer |-> TRUE]
    /\ hasPendingEvent = [p \in Peer |-> FALSE]
    /\ inputsReceived = {}

----
(**************************************************************************************************)
(* Lockstep frame advance actions                                                                 *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer submits input for current frame.                                      *)
(******************************************************************************)
SubmitInput(p) ==
    /\ p \notin inputsReceived
    /\ frame[p] = MinFrame
    /\ inputsReceived' = inputsReceived \union {p}
    /\ UNCHANGED <<electionVars, frameVars>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer advances to next frame after all inputs received.                     *)
(******************************************************************************)
AdvanceFrame(p) ==
    /\ inputsReceived = Peer
    /\ frame[p] < MaxFrame
    /\ frame[p] = MinFrame
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ inputsReceived' = IF \A q \in Peer : frame'[q] > MinFrame THEN {} ELSE inputsReceived
    /\ UNCHANGED <<electionVars, heartbeatReceived, hasPendingEvent>>

----
(**************************************************************************************************)
(* Owner-authoritative event actions                                                              *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer generates a local event.                                              *)
(******************************************************************************)
GenerateEvent(p) ==
    /\ ~hasPendingEvent[p]
    /\ hasPendingEvent' = [hasPendingEvent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<electionVars, frame, heartbeatReceived, inputsReceived>>

----
(**************************************************************************************************)
(* State sync actions                                                                             *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Leader sends state sync, atomically clearing follower events.              *)
(* Note: Simplified - real implementation has separate send/receive.          *)
(******************************************************************************)
SendStateSync(leader) ==
    /\ IsLeader(leader)
    /\ hasPendingEvent' = [p \in Peer |-> IF p = leader THEN hasPendingEvent[p] ELSE FALSE]
    /\ UNCHANGED <<electionVars, frame, heartbeatReceived, inputsReceived>>

----
(**************************************************************************************************)
(* Heartbeat actions                                                                              *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Leader broadcasts heartbeat to all peers.                                  *)
(******************************************************************************)
BroadcastHeartbeat(leader) ==
    /\ IsLeader(leader)
    /\ heartbeatReceived' = [p \in Peer |-> TRUE]
    /\ UNCHANGED <<electionVars, frame, hasPendingEvent, inputsReceived>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer's heartbeat timer expires (models timeout).                           *)
(******************************************************************************)
ExpireHeartbeat(p) ==
    /\ heartbeatReceived[p] = TRUE
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<electionVars, frame, hasPendingEvent, inputsReceived>>

----
(**************************************************************************************************)
(* Election actions                                                                               *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Follower starts election after heartbeat timeout.                          *)
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
    /\ UNCHANGED <<frame, hasPendingEvent, inputsReceived>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Voter grants vote to candidate.                                            *)
(******************************************************************************)
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
    /\ UNCHANGED <<frame, hasPendingEvent, inputsReceived>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Candidate wins election with majority votes.                               *)
(******************************************************************************)
BecomeLeader(p) ==
    /\ state[p] = "Candidate"
    /\ IsMajority(votesReceived[p])
    /\ state' = [state EXCEPT ![p] = "Leader"]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frameVars, inputsReceived>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Leader steps down upon seeing higher term.                                 *)
(******************************************************************************)
StepDown(p) ==
    /\ IsLeader(p)
    /\ \E q \in Peer : currentTerm[q] > currentTerm[p]
    /\ state' = [state EXCEPT ![p] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frame, hasPendingEvent, inputsReceived>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Candidate retries election after timeout.                                  *)
(******************************************************************************)
RetryElection(p) ==
    /\ state[p] = "Candidate"
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ UNCHANGED <<state, frameVars, inputsReceived>>

----
(**************************************************************************************************)
(* Specification                                                                                  *)
(**************************************************************************************************)

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
(**************************************************************************************************)
(* Safety invariants                                                                              *)
(**************************************************************************************************)

\* No two leaders in same term (election safety)
NoTwoLeadersInSameTerm ==
    \A i, j \in Peer :
        (i # j /\ IsLeader(i) /\ IsLeader(j)) => currentTerm[i] # currentTerm[j]

\* Frame drift bounded to 1
FrameBoundedDrift ==
    \A i, j \in Peer : frame[i] - frame[j] <= 1 /\ frame[j] - frame[i] <= 1

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] >= 0 /\ currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : state[p] \in {"Leader", "Follower", "Candidate"}
    /\ \A p \in Peer : hasPendingEvent[p] \in BOOLEAN

\* Leader is at most 1 frame behind any peer
LeaderUpToDate ==
    \A leader, p \in Peer : IsLeader(leader) => frame[leader] >= frame[p] - 1

\* If candidate, must have voted for self
CandidateVotedForSelf ==
    \A p \in Peer : state[p] = "Candidate" => votedFor[p] = p

\* If leader, must have voted for self
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

\* inputsReceived is a subset of Peer
InputsFromValidPeers ==
    inputsReceived \subseteq Peer

----
(**************************************************************************************************)
(* State constraint for finite model checking                                                     *)
(**************************************************************************************************)

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm

===============================================================================
