--------------------------------- MODULE LockstepNetwork ---------------------------------
\* P2P Lockstep with Message Loss and Simplified Election
\*
\* Verifies lockstep correctness under unreliable network:
\* 1. Lockstep frame synchronization with proper input tracking
\* 2. Message loss (unreliable DataChannel with maxRetransmits=0)
\* 3. Peer disconnect/reconnect
\* 4. Simplified leader election (leader can change, followers need sync)
\* 5. State sync from leader to recover desynced followers
\*
\* Implementation: client/src/network/LockstepNetcode.ts
\*
\* Target: ~10-50M states with 3 peers
\* ============================================================================

EXTENDS Integers, FiniteSets

\* The set of peer IDs
CONSTANT Peer

\* Model bounds
CONSTANT MaxFrame
CONSTANT MaxMessages

\* Initial leader
CONSTANT InitialLeader

(**************************************************************************************************)
(* Per-peer variables                                                                             *)
(**************************************************************************************************)

\* Whether peer is connected
VARIABLE connected

\* Current simulation frame per peer
VARIABLE frame

\* Who is the current leader (simplified: single global leader, not per-peer view)
VARIABLE leader

\* Whether peer needs state sync from leader (out of sync)
VARIABLE needsSync

\* Inputs received per peer for current frame: set of sender peer IDs
\* Key difference from before: tracks actual received inputs, not just network existence
VARIABLE inputsReceived

(**************************************************************************************************)
(* Network variables                                                                              *)
(**************************************************************************************************)

\* Set of in-flight messages: <<type, from, to, payload>>
\* Types: "input" (payload = frame), "sync" (payload = frame)
VARIABLE network

\* All variables
vars == <<connected, frame, leader, needsSync, inputsReceived, network>>

----
(**************************************************************************************************)
(* Helper operators                                                                               *)
(**************************************************************************************************)

ConnectedPeers == {p \in Peer : connected[p]}
ActivePeers == {p \in ConnectedPeers : ~needsSync[p]}  \* Connected and in sync
MinFrame == IF ActivePeers = {} THEN 0
            ELSE CHOOSE f \in {frame[p] : p \in ActivePeers} : \A q \in ActivePeers : frame[q] >= f

IsLeader(p) == leader = p
HasAllInputs(p) == \A q \in ActivePeers : q \in inputsReceived[p]

----
(**************************************************************************************************)
(* Initial state                                                                                  *)
(**************************************************************************************************)

Init ==
    /\ connected = [p \in Peer |-> TRUE]
    /\ frame = [p \in Peer |-> 0]
    /\ leader = InitialLeader
    /\ needsSync = [p \in Peer |-> FALSE]
    /\ inputsReceived = [p \in Peer |-> {p}]  \* Everyone has their own input
    /\ network = {}

----
(**************************************************************************************************)
(* Network actions                                                                                *)
(**************************************************************************************************)

(******************************************************************************)
(* Peer disconnects.                                                          *)
(* Guard: If leader disconnects, there must be another active peer to take over *)
(******************************************************************************)
Disconnect(p) ==
    /\ connected[p] = TRUE
    /\ Cardinality(ConnectedPeers) > 1
    \* If leader disconnects, must have another active peer to become leader
    /\ (p = leader) => (ActivePeers \ {p}) # {}
    /\ connected' = [connected EXCEPT ![p] = FALSE]
    \* Drop all messages to/from this peer
    /\ network' = {m \in network : m[2] # p /\ m[3] # p}
    \* If leader disconnects, pick an active peer as new leader
    /\ leader' = IF p = leader
                 THEN CHOOSE q \in ActivePeers \ {p} : TRUE
                 ELSE leader
    \* Disconnected peer will need sync when reconnecting
    /\ UNCHANGED <<frame, needsSync, inputsReceived>>

(******************************************************************************)
(* Peer reconnects - needs state sync before participating.                   *)
(******************************************************************************)
Reconnect(p) ==
    /\ connected[p] = FALSE
    /\ connected' = [connected EXCEPT ![p] = TRUE]
    /\ needsSync' = [needsSync EXCEPT ![p] = TRUE]  \* Must sync before active
    /\ inputsReceived' = [inputsReceived EXCEPT ![p] = {}]  \* Clear stale inputs
    /\ UNCHANGED <<frame, leader, network>>

(******************************************************************************)
(* Message is lost (unreliable network).                                      *)
(******************************************************************************)
LoseMessage(m) ==
    /\ m \in network
    /\ network' = network \ {m}
    /\ UNCHANGED <<connected, frame, leader, needsSync, inputsReceived>>

----
(**************************************************************************************************)
(* Lockstep actions                                                                               *)
(**************************************************************************************************)

(******************************************************************************)
(* Active peer broadcasts input for current frame.                            *)
(******************************************************************************)
BroadcastInput(p) ==
    /\ connected[p] = TRUE
    /\ ~needsSync[p]
    /\ frame[p] = MinFrame
    /\ LET newMsgs == {<<"input", p, q, frame[p]>> : q \in ActivePeers \ {p}}
       IN /\ Cardinality(network \union newMsgs) <= MaxMessages
          /\ network' = network \union newMsgs
    /\ UNCHANGED <<connected, frame, leader, needsSync, inputsReceived>>

(******************************************************************************)
(* Peer receives input message and records it.                                *)
(******************************************************************************)
ReceiveInput(p, m) ==
    /\ m \in network
    /\ m[1] = "input"
    /\ m[3] = p  \* Message is for us
    /\ connected[p] = TRUE
    /\ ~needsSync[p]
    /\ LET sender == m[2]
           msgFrame == m[4]
       IN /\ msgFrame = frame[p]  \* Only accept inputs for current frame
          /\ inputsReceived' = [inputsReceived EXCEPT ![p] = inputsReceived[p] \union {sender}]
    /\ network' = network \ {m}  \* Consume message
    /\ UNCHANGED <<connected, frame, leader, needsSync>>

(******************************************************************************)
(* Peer advances frame after receiving all inputs from active peers.          *)
(* Guard: No connected peer is waiting for sync (SC2-style pause on reconnect)*)
(******************************************************************************)
AdvanceFrame(p) ==
    /\ connected[p] = TRUE
    /\ ~needsSync[p]
    /\ frame[p] < MaxFrame
    /\ frame[p] = MinFrame
    /\ HasAllInputs(p)
    \* Don't advance while any connected peer needs sync
    /\ ~\E q \in ConnectedPeers : needsSync[q]
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ inputsReceived' = [inputsReceived EXCEPT ![p] = {p}]  \* Reset, keep own input
    /\ UNCHANGED <<connected, leader, needsSync, network>>

----
(**************************************************************************************************)
(* Leader election (simplified)                                                                   *)
(**************************************************************************************************)

(******************************************************************************)
(* Leadership changes to another connected peer.                              *)
(* Models: timeout, manual override, or network event.                        *)
(* New leader must be active (connected and in sync).                         *)
(******************************************************************************)
ChangeLeader(newLeader) ==
    /\ newLeader # leader
    /\ connected[newLeader] = TRUE
    /\ ~needsSync[newLeader]
    /\ frame[newLeader] >= MinFrame  \* Must be reasonably up-to-date
    /\ leader' = newLeader
    /\ UNCHANGED <<connected, frame, needsSync, inputsReceived, network>>

----
(**************************************************************************************************)
(* State sync actions                                                                             *)
(**************************************************************************************************)

(******************************************************************************)
(* Leader sends state sync to a peer that needs it.                           *)
(******************************************************************************)
SendStateSync(p) ==
    /\ IsLeader(leader)
    /\ connected[leader] = TRUE
    /\ connected[p] = TRUE
    /\ needsSync[p] = TRUE
    /\ p # leader
    /\ Cardinality(network) < MaxMessages
    /\ network' = network \union {<<"sync", leader, p, frame[leader]>>}
    /\ UNCHANGED <<connected, frame, leader, needsSync, inputsReceived>>

(******************************************************************************)
(* Peer receives state sync and becomes active.                               *)
(* Guard: Sync frame must be recent (within 1 of MinFrame) to avoid stale sync*)
(******************************************************************************)
ReceiveStateSync(p, m) ==
    /\ m \in network
    /\ m[1] = "sync"
    /\ m[3] = p
    /\ connected[p] = TRUE
    /\ needsSync[p] = TRUE
    /\ LET syncFrame == m[4]
       IN \* Reject stale syncs - must be within 1 frame of current min
          /\ syncFrame >= MinFrame - 1
          /\ frame' = [frame EXCEPT ![p] = syncFrame]
          /\ needsSync' = [needsSync EXCEPT ![p] = FALSE]
          /\ inputsReceived' = [inputsReceived EXCEPT ![p] = {p}]
    /\ network' = network \ {m}
    /\ UNCHANGED <<connected, leader>>

----
(**************************************************************************************************)
(* Specification                                                                                  *)
(**************************************************************************************************)

Next ==
    \* Network
    \/ \E p \in Peer : Disconnect(p)
    \/ \E p \in Peer : Reconnect(p)
    \/ \E m \in network : LoseMessage(m)
    \* Lockstep
    \/ \E p \in Peer : BroadcastInput(p)
    \/ \E p \in Peer : \E m \in network : ReceiveInput(p, m)
    \/ \E p \in Peer : AdvanceFrame(p)
    \* Election
    \/ \E p \in Peer : ChangeLeader(p)
    \* State sync
    \/ \E p \in Peer : SendStateSync(p)
    \/ \E p \in Peer : \E m \in network : ReceiveStateSync(p, m)

Fairness ==
    /\ WF_vars(\E p \in Peer : BroadcastInput(p))
    /\ WF_vars(\E p \in Peer : \E m \in network : ReceiveInput(p, m))
    /\ WF_vars(\E p \in Peer : AdvanceFrame(p))
    /\ WF_vars(\E p \in Peer : \E m \in network : ReceiveStateSync(p, m))

Spec == Init /\ [][Next]_vars /\ Fairness

----
(**************************************************************************************************)
(* Safety invariants                                                                              *)
(**************************************************************************************************)

\* Frame drift bounded to 1 among ACTIVE peers (connected and in sync)
FrameBoundedDrift ==
    \A i, j \in ActivePeers :
        frame[i] - frame[j] <= 1 /\ frame[j] - frame[i] <= 1

\* Leader is always an active peer (if any active peers exist)
LeaderIsActive ==
    ActivePeers # {} => (connected[leader] /\ ~needsSync[leader])

\* Leader's frame is at least MinFrame
LeaderUpToDate ==
    ActivePeers # {} => frame[leader] >= MinFrame

\* Peers needing sync don't have stale inputsReceived
NeedsSyncHasNoInputs ==
    \A p \in Peer : needsSync[p] => inputsReceived[p] = {}

\* Active peers always have at least their own input
ActiveHasOwnInput ==
    \A p \in ActivePeers : p \in inputsReceived[p]

\* Messages in network are valid
MessagesValid ==
    \A m \in network :
        /\ m[1] \in {"input", "sync"}
        /\ m[2] \in Peer
        /\ m[3] \in Peer
        /\ m[4] >= 0
        /\ m[4] <= MaxFrame

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : connected[p] \in BOOLEAN
    /\ \A p \in Peer : needsSync[p] \in BOOLEAN
    /\ \A p \in Peer : inputsReceived[p] \subseteq Peer
    /\ leader \in Peer
    /\ Cardinality(network) <= MaxMessages

----
(**************************************************************************************************)
(* Liveness properties                                                                            *)
(**************************************************************************************************)

\* If all peers stay connected and active, frames eventually advance
EventualProgress ==
    (\A p \in Peer : connected[p] /\ ~needsSync[p]) ~> (\E p \in Peer : frame[p] > 0)

\* Peers needing sync eventually get synced (if leader exists and is connected)
SyncEventuallyCompletes ==
    \A p \in Peer : (needsSync[p] /\ connected[p] /\ connected[leader]) ~> ~needsSync[p]

----
(**************************************************************************************************)
(* State constraint for finite model checking                                                     *)
(**************************************************************************************************)

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ Cardinality(network) <= MaxMessages

===============================================================================
