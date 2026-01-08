--------------------------------- MODULE LockstepMessageLoss ---------------------------------
\* P2P Lockstep with Message Loss
\*
\* Focused model for verifying lockstep correctness under unreliable network:
\* 1. Lockstep frame synchronization
\* 2. Message loss (unreliable DataChannel with maxRetransmits=0)
\* 3. Peer disconnect/reconnect
\* 4. Recovery via periodic re-broadcast (implementation does this each tick)
\*
\* DOES NOT MODEL (see separate specs):
\* - Leader election (see LeaderElection.tla)
\* - State sync with events (see LockstepState.tla)
\*
\* Implementation: client/src/network/LockstepNetcode.ts
\* - WebRTC DataChannel: ordered=false, maxRetransmits=0
\* - Each tick() calls broadcastInput() for current frame
\* - If inputs missing, waitingForInputs=true until received
\* - Recovery: leader's periodic state sync (abstracted here as Reconnect)
\*
\* Target: ~10-50M states with 3 peers
\* ============================================================================

EXTENDS Integers, FiniteSets

\* The set of peer IDs
CONSTANT Peer

\* Model bounds
CONSTANT MaxFrame
CONSTANT MaxMessages

(**************************************************************************************************)
(* Per-peer variables                                                                             *)
(**************************************************************************************************)

\* Whether peer is connected
VARIABLE connected

\* Current simulation frame per peer
VARIABLE frame

(**************************************************************************************************)
(* Network variables                                                                              *)
(**************************************************************************************************)

\* Set of in-flight input messages: <<from, to, frame>>
VARIABLE network

\* All variables
vars == <<connected, frame, network>>

----
(**************************************************************************************************)
(* Helper operators                                                                               *)
(**************************************************************************************************)

ConnectedPeers == {p \in Peer : connected[p]}
MinFrame == CHOOSE f \in {frame[p] : p \in ConnectedPeers} : \A q \in ConnectedPeers : frame[q] >= f

\* Peers whose input is needed for frame f
InputsNeededFor(f) == {p \in ConnectedPeers : frame[p] = f}

\* Count of inputs received for a given frame
InputsReceivedFor(receiver, f) ==
    {m \in network : m[2] = receiver /\ m[3] = f}

----
(**************************************************************************************************)
(* Initial state                                                                                  *)
(**************************************************************************************************)

Init ==
    /\ connected = [p \in Peer |-> TRUE]
    /\ frame = [p \in Peer |-> 0]
    /\ network = {}

----
(**************************************************************************************************)
(* Network actions                                                                                *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer disconnects.                                                          *)
(******************************************************************************)
Disconnect(p) ==
    /\ connected[p] = TRUE
    /\ Cardinality(ConnectedPeers) > 1  \* At least one peer must stay
    /\ connected' = [connected EXCEPT ![p] = FALSE]
    \* Drop all messages to/from this peer
    /\ network' = {m \in network : m[1] # p /\ m[2] # p}
    /\ UNCHANGED frame

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer reconnects at current min frame (state sync abstracted).              *)
(******************************************************************************)
Reconnect(p) ==
    /\ connected[p] = FALSE
    /\ connected' = [connected EXCEPT ![p] = TRUE]
    \* Reconnecting peer syncs to minimum frame (abstracts state sync)
    /\ frame' = [frame EXCEPT ![p] = MinFrame]
    /\ UNCHANGED network

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Message is lost.                                                           *)
(******************************************************************************)
LoseMessage(m) ==
    /\ m \in network
    /\ network' = network \ {m}
    /\ UNCHANGED <<connected, frame>>

----
(**************************************************************************************************)
(* Lockstep actions                                                                               *)
(**************************************************************************************************)

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer broadcasts input for current frame.                                   *)
(* Implementation: tick() -> broadcastInput() each frame                      *)
(*                                                                            *)
(* Re-broadcast is allowed because:                                           *)
(* 1. Implementation broadcasts every tick while waiting                      *)
(* 2. Receiver deduplicates (InputBuffer.storeInput overwrites)               *)
(* 3. Network uses set semantics (duplicate messages coalesce)                *)
(******************************************************************************)
BroadcastInput(p) ==
    /\ connected[p] = TRUE
    /\ frame[p] = MinFrame
    /\ Cardinality(network) < MaxMessages
    \* Broadcast to all other connected peers (re-broadcast allowed)
    /\ LET newMsgs == {<<p, q, frame[p]>> : q \in ConnectedPeers \ {p}}
       IN network' = network \union newMsgs
    /\ UNCHANGED <<connected, frame>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Peer advances frame after receiving all inputs.                            *)
(* "All inputs" means: one from each connected peer at current frame.         *)
(******************************************************************************)
AdvanceFrame(p) ==
    /\ connected[p] = TRUE
    /\ frame[p] < MaxFrame
    /\ frame[p] = MinFrame
    \* Must have received input from all other connected peers
    /\ \A q \in ConnectedPeers \ {p} : \E m \in network : m[1] = q /\ m[2] = p /\ m[3] = frame[p]
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    \* Consume messages for this frame to this peer
    /\ network' = {m \in network : ~(m[2] = p /\ m[3] = frame[p])}
    /\ UNCHANGED connected

----
(**************************************************************************************************)
(* Specification                                                                                  *)
(**************************************************************************************************)

Next ==
    \/ \E p \in Peer : Disconnect(p)
    \/ \E p \in Peer : Reconnect(p)
    \/ \E m \in network : LoseMessage(m)
    \/ \E p \in Peer : BroadcastInput(p)
    \/ \E p \in Peer : AdvanceFrame(p)

Fairness ==
    /\ WF_vars(\E p \in Peer : BroadcastInput(p))
    /\ WF_vars(\E p \in Peer : AdvanceFrame(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----
(**************************************************************************************************)
(* Safety invariants                                                                              *)
(**************************************************************************************************)

\* Frame drift bounded to 1 among connected peers
FrameBoundedDrift ==
    \A i, j \in ConnectedPeers :
        frame[i] - frame[j] <= 1 /\ frame[j] - frame[i] <= 1

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : connected[p] \in BOOLEAN
    /\ Cardinality(network) <= MaxMessages

\* Messages are between valid peers for valid frames
MessagesValid ==
    \A m \in network :
        /\ m[1] \in Peer
        /\ m[2] \in Peer
        /\ m[3] >= 0
        /\ m[3] <= MaxFrame

----
(**************************************************************************************************)
(* Liveness properties                                                                            *)
(**************************************************************************************************)

\* If all peers stay connected, frames eventually advance
\* (fairness on BroadcastInput ensures re-broadcasts overcome message loss)
EventualProgress ==
    (\A p \in Peer : connected[p]) ~> (\E p \in Peer : frame[p] > 0)

\* Frames continue advancing (not just the first frame)
\* Requires: no sustained message loss (WF on BroadcastInput)
ContinuousProgress ==
    []<>(\A p \in ConnectedPeers : frame[p] < MaxFrame =>
         <>(\E q \in ConnectedPeers : frame[q] > frame[p]))

----
(**************************************************************************************************)
(* State constraint for finite model checking                                                     *)
(**************************************************************************************************)

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ Cardinality(network) <= MaxMessages

===============================================================================
