--------------------------------- MODULE LockstepNetwork ---------------------------------
\* P2P Lockstep Netcode with Network Layer
\*
\* Combines protocol correctness (from LockstepState) with network realism:
\* 1. Lockstep frame synchronization
\* 2. Raft-inspired leader election
\* 3. Owner-authoritative events with tuple tracking
\* 4. Async state sync with term validation
\* 5. Message network with loss
\* 6. Network partitions (symmetric)
\* 7. Peer disconnect/reconnect
\*
\* Implementation: client/src/network/
\*
\* ============================================================================
\* DESIGN DECISIONS
\* ============================================================================
\*
\* INCLUDED (from LockstepState):
\* - Async state sync: SendStateSync and ReceiveStateSync are separate
\* - Tuple events: pendingEvents is set of <<owner, frame>> tuples
\* - Term validation: syncTerm prevents accepting stale syncs
\* - LocalEventsPreserved invariant
\*
\* INCLUDED (network layer):
\* - Message loss: Messages can be dropped (unreliable DataChannel)
\* - Partitions: Symmetric partitions between peer pairs
\* - Composite mode: 5 explicit states (Disconnected/Syncing/Active/Electing/Leading)
\*
\* EXCLUDED (intentional simplifications):
\* - ICE restart: Implementation detail, doesn't affect protocol semantics
\* - Message reordering: Lockstep tolerates via frame numbers (wrong frame ignored)
\* - Message duplication: Idempotent receive (sets are deduplicated)
\* - WebRTC signaling states: Simplified to mode (composite state)
\* - Checksum collision: Abstract Syncing/Active mode suffices
\* - Connection flapping: Would explode state space
\*
\* Target: ~20-50M states with 3 peers
\* ============================================================================

EXTENDS Integers, FiniteSets

\* The set of peer IDs
CONSTANT Peer

\* Model bounds
CONSTANT MaxFrame
CONSTANT MaxTerm
CONSTANT MaxEvents
CONSTANT MaxMessages

\* First peer to be leader (typically the host)
CONSTANT InitialLeader

(**************************************************************************************************)
(* Peer mode                                                                                      *)
(*                                                                                                *)
(* Composite state replacing separate connected/state/inSync variables:                           *)
(*   Disconnected - Peer offline (WebRTC connection failed)                                       *)
(*   Syncing     - Connected but waiting for state sync from leader                               *)
(*   Active      - Connected follower, in sync with leader                                        *)
(*   Electing    - Connected candidate, running for leader                                        *)
(*   Leading     - Connected leader, broadcasting state syncs                                     *)
(**************************************************************************************************)
Mode == {"Disconnected", "Syncing", "Active", "Electing", "Leading"}

(**************************************************************************************************)
(* Per-peer variables                                                                             *)
(**************************************************************************************************)

\* Peer's operational mode (replaces connected, state, inSync)
VARIABLE mode

\* The peer's current election term
VARIABLE currentTerm

\* Who this peer voted for in current term (0 = none)
VARIABLE votedFor

\* Votes received by this peer (when candidate)
VARIABLE votesReceived

electionVars == <<currentTerm, mode, votedFor, votesReceived>>

\* Current simulation frame per peer
VARIABLE frame

\* Whether heartbeat was received this round
VARIABLE heartbeatReceived

\* Term of last accepted state sync (for validation)
VARIABLE syncTerm

\* Pending events per peer: set of <<owner, frame>> tuples
VARIABLE pendingEvents

syncVars == <<syncTerm, pendingEvents>>

frameVars == <<frame, heartbeatReceived>>

(**************************************************************************************************)
(* Global variables                                                                               *)
(**************************************************************************************************)

\* Peers who submitted input for current frame
VARIABLE inputsReceived

(**************************************************************************************************)
(* Network variables                                                                              *)
(**************************************************************************************************)

\* Set of in-flight messages
VARIABLE network

\* Symmetric partition: partitioned[{p,q}] = TRUE
VARIABLE partitioned

networkVars == <<network, partitioned>>

\* All variables
protocolVars == <<electionVars, frameVars, syncVars, inputsReceived>>
vars == <<protocolVars, networkVars>>

----
(**************************************************************************************************)
(* Message types                                                                                  *)
(*                                                                                                *)
(* Messages are tuples: <<type, from, to, payload...>>                                            *)
(* Types:                                                                                         *)
(*   "input"      - <<from, to, frame>>                                                           *)
(*   "state_sync" - <<from, to, term, frame>>                                                     *)
(*   "heartbeat"  - <<from, to, term>>                                                            *)
(*   "vote_req"   - <<from, to, term, lastFrame>>                                                 *)
(*   "vote_resp"  - <<from, to, term, granted>>                                                   *)
(**************************************************************************************************)

MsgType(m) == m[1]
MsgFrom(m) == m[2]
MsgTo(m) == m[3]

----
(**************************************************************************************************)
(* Helper operators                                                                               *)
(**************************************************************************************************)

IsMajority(votes) == Cardinality(votes) * 2 > Cardinality(Peer)
MinFrame == CHOOSE f \in {frame[p] : p \in Peer} : \A q \in Peer : frame[q] >= f

\* Mode helpers
IsConnected(p) == mode[p] # "Disconnected"
IsLeader(p) == mode[p] = "Leading"
IsCandidate(p) == mode[p] = "Electing"
IsFollower(p) == mode[p] \in {"Active", "Syncing"}
IsSyncing(p) == mode[p] = "Syncing"
IsActive(p) == mode[p] = "Active"

\* Connected peers only
ConnectedPeers == {p \in Peer : IsConnected(p)}

\* Check if two peers can communicate (both connected, not partitioned)
CanCommunicate(p, q) ==
    /\ IsConnected(p)
    /\ IsConnected(q)
    /\ ~partitioned[{p, q}]

\* All partition pairs (unordered)
PartitionPairs == {{p, q} : p, q \in Peer}

----
(**************************************************************************************************)
(* Initial state                                                                                  *)
(**************************************************************************************************)

Init ==
    \* Mode: Leader starts as Leading, others as Active (connected, in sync)
    /\ mode = [p \in Peer |-> IF p = InitialLeader THEN "Leading" ELSE "Active"]
    \* Election state
    /\ currentTerm = [p \in Peer |-> 0]
    /\ votedFor = [p \in Peer |-> IF p = InitialLeader THEN p ELSE 0]
    /\ votesReceived = [p \in Peer |-> {}]
    \* Frame state
    /\ frame = [p \in Peer |-> 0]
    /\ heartbeatReceived = [p \in Peer |-> TRUE]
    \* Sync state
    /\ syncTerm = [p \in Peer |-> 0]
    /\ pendingEvents = [p \in Peer |-> {}]
    \* Global state
    /\ inputsReceived = {}
    \* Network state
    /\ network = {}
    /\ partitioned = [pair \in PartitionPairs |-> FALSE]

----
(**************************************************************************************************)
(* Network actions                                                                                *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer disconnects (models WebRTC connection failure).                       *)
(******************************************************************************)
Disconnect(p) ==
    /\ IsConnected(p)
    /\ mode' = [mode EXCEPT ![p] = "Disconnected"]
    \* Drop all messages to/from this peer
    /\ network' = {m \in network : MsgFrom(m) # p /\ MsgTo(m) # p}
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frameVars, syncVars, inputsReceived>>
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer reconnects.                                                           *)
(******************************************************************************)
Reconnect(p) ==
    /\ mode[p] = "Disconnected"
    \* Reconnecting peer needs state sync
    /\ mode' = [mode EXCEPT ![p] = "Syncing"]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frameVars, syncVars, inputsReceived>>
    /\ UNCHANGED <<network, partitioned>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Create partition between two peers (symmetric).                            *)
(******************************************************************************)
CreatePartition(p, q) ==
    /\ p # q
    /\ ~partitioned[{p, q}]
    /\ partitioned' = [partitioned EXCEPT ![{p, q}] = TRUE]
    \* Drop messages between partitioned peers
    /\ network' = {m \in network :
         ~((MsgFrom(m) = p /\ MsgTo(m) = q) \/ (MsgFrom(m) = q /\ MsgTo(m) = p))}
    /\ UNCHANGED protocolVars

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Heal partition between two peers.                                          *)
(******************************************************************************)
HealPartition(p, q) ==
    /\ p # q
    /\ partitioned[{p, q}]
    /\ partitioned' = [partitioned EXCEPT ![{p, q}] = FALSE]
    /\ UNCHANGED protocolVars
    /\ UNCHANGED network

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Message is lost (unreliable network).                                      *)
(******************************************************************************)
LoseMessage(m) ==
    /\ m \in network
    /\ network' = network \ {m}
    /\ UNCHANGED protocolVars
    /\ UNCHANGED partitioned

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
    /\ IsConnected(p)
    /\ p \notin inputsReceived
    /\ frame[p] = MinFrame
    /\ Cardinality(network) < MaxMessages
    /\ inputsReceived' = inputsReceived \union {p}
    \* Broadcast input message to all connected peers
    /\ LET newMsgs == {<<"input", p, q, frame[p]>> : q \in ConnectedPeers \ {p}}
       IN network' = network \union newMsgs
    /\ UNCHANGED <<electionVars, frameVars, syncVars>>
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer receives input message.                                               *)
(******************************************************************************)
ReceiveInput(m) ==
    /\ m \in network
    /\ MsgType(m) = "input"
    /\ LET sender == MsgFrom(m)
           receiver == MsgTo(m)
           msgFrame == m[4]
       IN /\ IsConnected(receiver)
          /\ CanCommunicate(sender, receiver)
          \* Input is useful if it's for our current frame
          /\ msgFrame = frame[receiver]
          /\ sender \notin inputsReceived
          /\ inputsReceived' = inputsReceived \union {sender}
    /\ network' = network \ {m}
    /\ UNCHANGED <<electionVars, frameVars, syncVars>>
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer advances to next frame after all inputs received.                     *)
(******************************************************************************)
AdvanceFrame(p) ==
    /\ IsConnected(p)
    /\ inputsReceived = ConnectedPeers  \* All connected peers submitted
    /\ frame[p] < MaxFrame
    /\ frame[p] = MinFrame
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    \* Reset inputsReceived when all peers have advanced
    /\ inputsReceived' = IF \A q \in ConnectedPeers : frame'[q] > MinFrame
                         THEN {}
                         ELSE inputsReceived
    /\ UNCHANGED <<electionVars, heartbeatReceived, syncVars>>
    /\ UNCHANGED networkVars

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
    /\ IsConnected(p)
    /\ Cardinality(pendingEvents[p]) < MaxEvents
    /\ pendingEvents' = [pendingEvents EXCEPT ![p] = pendingEvents[p] \union {<<p, frame[p]>>}]
    /\ UNCHANGED <<electionVars, frameVars, syncTerm, inputsReceived>>
    /\ UNCHANGED networkVars

----
(**************************************************************************************************)
(* State sync actions                                                                             *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Leader sends state sync to followers.                                      *)
(******************************************************************************)
SendStateSync(leader) ==
    /\ IsLeader(leader)
    /\ Cardinality(network) < MaxMessages
    \* Send sync message to all connected followers
    /\ LET newMsgs == {<<"state_sync", leader, q, currentTerm[leader], frame[leader]>>
                       : q \in ConnectedPeers \ {leader}}
       IN network' = network \union newMsgs
    /\ UNCHANGED protocolVars
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Non-leader receives state sync from leader.                                *)
(* Key: Remote events cleared, LOCAL events preserved.                        *)
(* Candidates step down, clears election state.                               *)
(* Transitions any non-leader -> Active.                                      *)
(******************************************************************************)
ReceiveStateSync(m) ==
    /\ m \in network
    /\ MsgType(m) = "state_sync"
    /\ LET sender == MsgFrom(m)
           receiver == MsgTo(m)
           msgTerm == m[4]
           msgFrame == m[5]
       IN /\ IsConnected(receiver)
          /\ ~IsLeader(receiver)  \* Leaders don't accept syncs
          /\ CanCommunicate(sender, receiver)
          \* Term validation: only accept from current or higher term
          /\ msgTerm >= syncTerm[receiver]
          \* Transition to Active (in sync with leader) - candidates step down
          /\ mode' = [mode EXCEPT ![receiver] = "Active"]
          /\ currentTerm' = [currentTerm EXCEPT ![receiver] = IF msgTerm > currentTerm[receiver] THEN msgTerm ELSE currentTerm[receiver]]
          \* Clear votes - cannot use old votes in new term
          /\ votesReceived' = [votesReceived EXCEPT ![receiver] = {}]
          \* Reset votedFor on term change (can vote again in new term)
          /\ votedFor' = [votedFor EXCEPT ![receiver] = IF msgTerm > currentTerm[receiver] THEN 0 ELSE votedFor[receiver]]
          /\ syncTerm' = [syncTerm EXCEPT ![receiver] = msgTerm]
          \* KEY: Filter to keep only events owned by receiver
          /\ pendingEvents' = [pendingEvents EXCEPT
               ![receiver] = {e \in pendingEvents[receiver] : e[1] = receiver}]
    /\ network' = network \ {m}
    /\ UNCHANGED <<frame, inputsReceived, heartbeatReceived>>
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer detects state divergence (checksum mismatch).                         *)
(* Transitions Active -> Syncing.                                             *)
(******************************************************************************)
Desync(p) ==
    /\ IsActive(p)  \* Only Active followers can desync
    /\ mode' = [mode EXCEPT ![p] = "Syncing"]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frameVars, syncVars, inputsReceived>>
    /\ UNCHANGED networkVars

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
    /\ Cardinality(network) < MaxMessages
    \* Send heartbeat to all connected peers
    /\ LET newMsgs == {<<"heartbeat", leader, q, currentTerm[leader]>>
                       : q \in ConnectedPeers \ {leader}}
       IN network' = network \union newMsgs
    \* Leader's own heartbeat is always "received"
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![leader] = TRUE]
    /\ UNCHANGED <<electionVars, frame, syncVars, inputsReceived>>
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer receives heartbeat from leader.                                       *)
(* Non-followers step down to Syncing (need state sync from new leader).      *)
(******************************************************************************)
ReceiveHeartbeat(m) ==
    /\ m \in network
    /\ MsgType(m) = "heartbeat"
    /\ LET sender == MsgFrom(m)
           receiver == MsgTo(m)
           msgTerm == m[4]
       IN /\ IsConnected(receiver)
          /\ CanCommunicate(sender, receiver)
          /\ msgTerm >= currentTerm[receiver]
          \* Accept heartbeat: Leaders/Candidates step down to Syncing, Active stays Active
          /\ mode' = [mode EXCEPT ![receiver] =
               CASE IsLeader(receiver)    -> "Syncing"    \* Leader steps down
                 [] IsCandidate(receiver) -> "Syncing"    \* Candidate steps down
                 [] IsActive(receiver)    -> "Active"     \* Stay in sync
                 [] OTHER                 -> "Syncing"]   \* Syncing stays Syncing
          /\ currentTerm' = [currentTerm EXCEPT ![receiver] = msgTerm]
          /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![receiver] = TRUE]
    /\ network' = network \ {m}
    /\ UNCHANGED <<frame, votedFor, votesReceived, inputsReceived, syncVars>>
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer's heartbeat timer expires (models timeout).                           *)
(******************************************************************************)
ExpireHeartbeat(p) ==
    /\ IsConnected(p)
    /\ heartbeatReceived[p] = TRUE
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<electionVars, frame, syncVars, inputsReceived>>
    /\ UNCHANGED networkVars

----
(**************************************************************************************************)
(* Election actions                                                                               *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Follower starts election after heartbeat timeout.                          *)
(* Transitions Active/Syncing -> Electing.                                    *)
(******************************************************************************)
StartElection(p) ==
    /\ IsFollower(p)  \* Active or Syncing
    /\ heartbeatReceived[p] = FALSE
    /\ currentTerm[p] < MaxTerm
    /\ Cardinality(network) < MaxMessages
    /\ mode' = [mode EXCEPT ![p] = "Electing"]
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = TRUE]
    \* Send vote requests
    /\ LET newMsgs == {<<"vote_req", p, q, currentTerm'[p], frame[p]>>
                       : q \in ConnectedPeers \ {p}}
       IN network' = network \union newMsgs
    /\ UNCHANGED <<frame, syncVars, inputsReceived>>
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer receives vote request and grants vote.                                *)
(* Non-Active voters step down to Syncing.                                    *)
(******************************************************************************)
ReceiveVoteRequest(m) ==
    /\ m \in network
    /\ MsgType(m) = "vote_req"
    /\ LET candidate == MsgFrom(m)
           voter == MsgTo(m)
           msgTerm == m[4]
           lastFrame == m[5]
       IN /\ IsConnected(voter)
          /\ CanCommunicate(candidate, voter)
          /\ msgTerm >= currentTerm[voter]
          /\ lastFrame >= frame[voter]  \* Log comparison
          /\ \/ votedFor[voter] = 0
             \/ msgTerm > currentTerm[voter]
          \* Grant vote: non-Active modes step down to Syncing
          /\ mode' = [mode EXCEPT ![voter] =
               CASE IsLeader(voter)    -> "Syncing"    \* Leader steps down
                 [] IsCandidate(voter) -> "Syncing"    \* Candidate steps down
                 [] IsActive(voter)    -> "Active"     \* Stay in sync
                 [] OTHER              -> "Syncing"]   \* Syncing stays Syncing
          /\ votedFor' = [votedFor EXCEPT ![voter] = candidate]
          /\ currentTerm' = [currentTerm EXCEPT ![voter] = msgTerm]
          /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![voter] = TRUE]
          \* Send vote response
          /\ network' = (network \ {m}) \union
               {<<"vote_resp", voter, candidate, msgTerm, TRUE>>}
    /\ UNCHANGED <<frame, votesReceived, syncVars, inputsReceived>>
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Candidate receives vote response.                                          *)
(******************************************************************************)
ReceiveVoteResponse(m) ==
    /\ m \in network
    /\ MsgType(m) = "vote_resp"
    /\ LET voter == MsgFrom(m)
           candidate == MsgTo(m)
           msgTerm == m[4]
           granted == m[5]
       IN /\ IsConnected(candidate)
          /\ CanCommunicate(voter, candidate)
          /\ IsCandidate(candidate)
          /\ msgTerm = currentTerm[candidate]
          /\ granted = TRUE
          /\ votesReceived' = [votesReceived EXCEPT
               ![candidate] = votesReceived[candidate] \union {voter}]
    /\ network' = network \ {m}
    /\ UNCHANGED <<currentTerm, mode, votedFor, frameVars, syncVars, inputsReceived>>
    /\ UNCHANGED partitioned

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Candidate wins election with majority votes.                               *)
(* Transitions Electing -> Leading.                                           *)
(******************************************************************************)
BecomeLeader(p) ==
    /\ IsCandidate(p)
    /\ IsMajority(votesReceived[p])
    /\ mode' = [mode EXCEPT ![p] = "Leading"]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frameVars, syncVars, inputsReceived>>
    /\ UNCHANGED networkVars

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Leader steps down upon seeing higher term.                                 *)
(* Transitions Leading -> Syncing (needs sync from new leader).               *)
(******************************************************************************)
StepDown(p) ==
    /\ IsLeader(p)
    /\ \E q \in Peer : currentTerm[q] > currentTerm[p]
    /\ mode' = [mode EXCEPT ![p] = "Syncing"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frame, syncVars, inputsReceived>>
    /\ UNCHANGED networkVars

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Candidate retries election after timeout.                                  *)
(******************************************************************************)
RetryElection(p) ==
    /\ IsCandidate(p)
    /\ currentTerm[p] < MaxTerm
    /\ Cardinality(network) < MaxMessages
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    \* Send new vote requests
    /\ LET newMsgs == {<<"vote_req", p, q, currentTerm'[p], frame[p]>>
                       : q \in ConnectedPeers \ {p}}
       IN network' = network \union newMsgs
    /\ UNCHANGED <<mode, frameVars, syncVars, inputsReceived>>
    /\ UNCHANGED partitioned

----
(**************************************************************************************************)
(* Specification                                                                                  *)
(**************************************************************************************************)

Next ==
    \* Network layer
    \/ \E p \in Peer : Disconnect(p)
    \/ \E p \in Peer : Reconnect(p)
    \/ \E p, q \in Peer : CreatePartition(p, q)
    \/ \E p, q \in Peer : HealPartition(p, q)
    \/ \E m \in network : LoseMessage(m)
    \* Lockstep
    \/ \E p \in Peer : SubmitInput(p)
    \/ \E m \in network : ReceiveInput(m)
    \/ \E p \in Peer : AdvanceFrame(p)
    \* Events
    \/ \E p \in Peer : GenerateEvent(p)
    \* State Sync
    \/ \E p \in Peer : SendStateSync(p)
    \/ \E m \in network : ReceiveStateSync(m)
    \/ \E p \in Peer : Desync(p)
    \* Election
    \/ \E p \in Peer : BroadcastHeartbeat(p)
    \/ \E m \in network : ReceiveHeartbeat(m)
    \/ \E p \in Peer : ExpireHeartbeat(p)
    \/ \E p \in Peer : StartElection(p)
    \/ \E m \in network : ReceiveVoteRequest(m)
    \/ \E m \in network : ReceiveVoteResponse(m)
    \/ \E p \in Peer : BecomeLeader(p)
    \/ \E p \in Peer : StepDown(p)
    \/ \E p \in Peer : RetryElection(p)

Fairness ==
    \* Progress guarantees
    /\ WF_vars(\E p \in Peer : SubmitInput(p))
    /\ WF_vars(\E m \in network : ReceiveInput(m))
    /\ WF_vars(\E p \in Peer : AdvanceFrame(p))
    /\ WF_vars(\E p \in Peer : BroadcastHeartbeat(p))
    /\ WF_vars(\E m \in network : ReceiveHeartbeat(m))
    /\ WF_vars(\E p \in Peer : BecomeLeader(p))
    /\ WF_vars(\E m \in network : ReceiveStateSync(m))
    /\ WF_vars(\E p, q \in Peer : HealPartition(p, q))

Spec == Init /\ [][Next]_vars /\ Fairness

----
(**************************************************************************************************)
(* Safety invariants                                                                              *)
(**************************************************************************************************)

\* No two leaders in same term (election safety)
NoTwoLeadersInSameTerm ==
    \A i, j \in Peer :
        (i # j /\ IsLeader(i) /\ IsLeader(j)) => currentTerm[i] # currentTerm[j]

\* Frame drift bounded to 1 among connected peers
FrameBoundedDrift ==
    \A i, j \in ConnectedPeers :
        frame[i] - frame[j] <= 1 /\ frame[j] - frame[i] <= 1

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] >= 0 /\ currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : syncTerm[p] >= 0 /\ syncTerm[p] <= MaxTerm
    /\ \A p \in Peer : mode[p] \in Mode
    /\ \A p \in Peer : Cardinality(pendingEvents[p]) <= MaxEvents
    /\ Cardinality(network) <= MaxMessages

\* Leader is at most 1 frame behind connected peers
LeaderUpToDate ==
    \A leader, p \in ConnectedPeers :
        IsLeader(leader) => frame[leader] >= frame[p] - 1

\* After state sync, pending events contain ONLY local events
LocalEventsPreserved ==
    \A p \in Peer : \A e \in pendingEvents[p] : e[1] = p

\* Sync term never exceeds current term
SyncTermBounded ==
    \A p \in Peer : syncTerm[p] <= currentTerm[p]

\* If candidate, must have voted for self
CandidateVotedForSelf ==
    \A p \in Peer : IsCandidate(p) => votedFor[p] = p

\* If leader, must have voted for self
LeaderVotedForSelf ==
    \A p \in Peer : IsLeader(p) => votedFor[p] = p

\* All messages are between valid peers
MessagesValid ==
    \A m \in network : MsgFrom(m) \in Peer /\ MsgTo(m) \in Peer

\* No self-partition (sanity check)
NoSelfPartition ==
    \A p \in Peer : ~partitioned[{p, p}]

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
(* Liveness properties                                                                            *)
(**************************************************************************************************)

\* Eventually there is a leader (among connected peers)
EventuallyLeader ==
    <>(\E p \in ConnectedPeers : IsLeader(p))

\* Desync is eventually corrected via state sync (Syncing -> Active)
DesyncEventuallyCorrected ==
    (\E p \in Peer : IsLeader(p)) =>
        <>(\A p \in ConnectedPeers : ~IsSyncing(p))

\* Partitions eventually heal
PartitionsEventuallyHeal ==
    <>(\A pair \in PartitionPairs : ~partitioned[pair])

----
(**************************************************************************************************)
(* State constraint for finite model checking                                                     *)
(**************************************************************************************************)

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : Cardinality(pendingEvents[p]) <= MaxEvents
    /\ Cardinality(network) <= MaxMessages

===============================================================================
