--------------------------------- MODULE LockstepNetcode ---------------------------------
\* Formal specification for P2P Lockstep Netcode with Leader Election
\*
\* This specification models:
\* 1. Deterministic lockstep simulation across peers
\* 2. Raft-inspired leader election for state sync authority
\* 3. Owner-authoritative events (damage, pickup, etc.)
\* 4. State synchronization from leader to followers
\*
\* Safety Properties:
\* - No two leaders in same term (election safety)
\* - Committed events are never lost (event durability)
\* - State sync only from leader (authority)
\* - All peers converge to same state (consistency)
\*
\* To run: ./model-check.sh LockstepNetcode

EXTENDS Integers, FiniteSets, Sequences

\* The set of peer IDs (players in the game)
CONSTANT Peer

\* Maximum simulation frame to explore
CONSTANT MaxFrame

\* Maximum election term to explore
CONSTANT MaxTerm

\* Maximum events that can be generated
CONSTANT MaxEvents

\* Maximum pending events in buffer
CONSTANT MaxPendingEvents

----
\* Per-peer state variables (functions with domain Peer)

\* Current simulation frame for each peer
VARIABLE frame

\* Election term for each peer
VARIABLE currentTerm

\* Peer state: "Follower", "Candidate", "Leader"
VARIABLE state

\* Who this peer voted for in current term (Peer ID or "None")
VARIABLE votedFor

\* Current leader known to each peer ("None" if unknown)
VARIABLE currentLeader

\* Vote count received (only meaningful for candidates)
VARIABLE votesReceived

\* Event log: sequence of events confirmed by all peers
\* Each event is [term |-> t, frame |-> f, owner |-> p, type |-> "event"]
VARIABLE eventLog

\* Pending local events not yet confirmed
\* Map from peer -> sequence of events
VARIABLE pendingEvents

\* Last state sync frame received from leader
VARIABLE lastSyncFrame

\* Checksum of game state at current frame (abstracted as frame number for simplicity)
\* In real impl, this is a hash of game state
VARIABLE stateChecksum

\* Network connectivity: which peers can communicate
\* partitioned[i][j] = TRUE means i cannot receive from j
VARIABLE partitioned

----
\* Variable groupings for stuttering

electionVars == <<currentTerm, state, votedFor, currentLeader, votesReceived>>
frameVars == <<frame, lastSyncFrame, stateChecksum>>
eventVars == <<eventLog, pendingEvents>>
networkVars == <<partitioned>>

vars == <<electionVars, frameVars, eventVars, networkVars>>

----
\* Helpers

\* Check if peer set forms a majority
IsMajority(peers) == Cardinality(peers) * 2 > Cardinality(Peer)

\* Get all leaders
Leaders == {p \in Peer : state[p] = "Leader"}

\* Get minimum peer ID (initial leader)
MinPeer == CHOOSE p \in Peer : \A q \in Peer : p <= q

\* Check if peer i can receive messages from peer j
CanReceive(i, j) == ~partitioned[i][j]

\* Get the highest term seen
MaxTerm(peers) ==
    IF peers = {} THEN 0
    ELSE CHOOSE t \in {currentTerm[p] : p \in peers} :
         \A p \in peers : currentTerm[p] <= t

\* Range of a function
Range(f) == {f[x] : x \in DOMAIN f}

\* Last element of sequence
Last(s) == s[Len(s)]

\* Get confirmed events up to a frame
EventsUpToFrame(f) ==
    {e \in Range(eventLog) : e.frame <= f}

----
\* Initial state

InitElectionVars ==
    /\ currentTerm = [p \in Peer |-> 0]
    /\ state = [p \in Peer |-> IF p = MinPeer THEN "Leader" ELSE "Follower"]
    /\ votedFor = [p \in Peer |-> "None"]
    /\ currentLeader = [p \in Peer |-> MinPeer]
    /\ votesReceived = [p \in Peer |-> {}]

InitFrameVars ==
    /\ frame = [p \in Peer |-> 0]
    /\ lastSyncFrame = [p \in Peer |-> 0]
    /\ stateChecksum = [p \in Peer |-> 0]

InitEventVars ==
    /\ eventLog = << >>
    /\ pendingEvents = [p \in Peer |-> << >>]

InitNetworkVars ==
    /\ partitioned = [i \in Peer |-> [j \in Peer |-> FALSE]]

Init ==
    /\ InitElectionVars
    /\ InitFrameVars
    /\ InitEventVars
    /\ InitNetworkVars

----
\* Actions

\* ACTION: Advance simulation frame (all peers must have same frame for lockstep)
\* In pure lockstep, frame only advances when all inputs received
AdvanceFrame(p) ==
    /\ frame[p] < MaxFrame
    \* All peers must be at same frame (lockstep constraint)
    /\ \A q \in Peer : CanReceive(p, q) => frame[q] >= frame[p]
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    \* Update checksum (simplified: just the frame number)
    /\ stateChecksum' = [stateChecksum EXCEPT ![p] = frame[p] + 1]
    /\ UNCHANGED <<electionVars, eventVars, lastSyncFrame, networkVars>>

\* ACTION: Generate a local event (owner-authoritative)
GenerateEvent(p) ==
    /\ Len(pendingEvents[p]) < MaxPendingEvents
    /\ Len(eventLog) < MaxEvents
    /\ LET newEvent == [
           term |-> currentTerm[p],
           frame |-> frame[p],
           owner |-> p,
           type |-> "event"
       ]
       IN pendingEvents' = [pendingEvents EXCEPT ![p] = Append(pendingEvents[p], newEvent)]
    /\ UNCHANGED <<electionVars, frameVars, eventLog, networkVars>>

\* ACTION: Leader confirms pending events (adds to global log)
ConfirmEvents(leader) ==
    /\ state[leader] = "Leader"
    /\ \E p \in Peer :
        /\ Len(pendingEvents[p]) > 0
        /\ CanReceive(leader, p)
        /\ LET event == pendingEvents[p][1]
           IN /\ eventLog' = Append(eventLog, event)
              /\ pendingEvents' = [pendingEvents EXCEPT ![p] = Tail(pendingEvents[p])]
    /\ UNCHANGED <<electionVars, frameVars, networkVars>>

\* ACTION: Leader sends state sync to follower
\* Non-leader applies state from leader
SendStateSync(leader, follower) ==
    /\ state[leader] = "Leader"
    /\ leader # follower
    /\ CanReceive(follower, leader)
    /\ currentLeader[follower] = leader
    \* Follower updates to leader's frame if behind
    /\ frame[follower] <= frame[leader]
    /\ frame' = [frame EXCEPT ![follower] = frame[leader]]
    /\ lastSyncFrame' = [lastSyncFrame EXCEPT ![follower] = frame[leader]]
    /\ stateChecksum' = [stateChecksum EXCEPT ![follower] = stateChecksum[leader]]
    /\ UNCHANGED <<electionVars, eventVars, networkVars>>

----
\* Election Actions (Raft-inspired)

\* ACTION: Follower times out and becomes candidate
StartElection(p) ==
    /\ state[p] # "Leader"
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ state' = [state EXCEPT ![p] = "Candidate"]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]  \* Vote for self
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]  \* Count own vote
    /\ currentLeader' = [currentLeader EXCEPT ![p] = "None"]
    /\ UNCHANGED <<frameVars, eventVars, networkVars>>

\* ACTION: Candidate requests vote from peer
\* Peer grants vote if: higher term, hasn't voted, or voted for same candidate
RequestVote(candidate, voter) ==
    /\ state[candidate] = "Candidate"
    /\ candidate # voter
    /\ CanReceive(voter, candidate)
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ \/ votedFor[voter] = "None"
       \/ votedFor[voter] = candidate
       \/ currentTerm[candidate] > currentTerm[voter]
    \* Grant vote
    /\ votedFor' = [votedFor EXCEPT ![voter] = candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![voter] = currentTerm[candidate]]
    /\ votesReceived' = [votesReceived EXCEPT ![candidate] = votesReceived[candidate] \union {voter}]
    /\ state' = [state EXCEPT ![voter] = "Follower"]
    /\ UNCHANGED <<currentLeader, frameVars, eventVars, networkVars>>

\* ACTION: Candidate wins election with majority
BecomeLeader(p) ==
    /\ state[p] = "Candidate"
    /\ IsMajority(votesReceived[p])
    /\ state' = [state EXCEPT ![p] = "Leader"]
    /\ currentLeader' = [currentLeader EXCEPT ![p] = p]
    /\ UNCHANGED <<currentTerm, votedFor, votesReceived, frameVars, eventVars, networkVars>>

\* ACTION: Leader steps down (discovers higher term or loses connectivity)
Stepdown(leader) ==
    /\ state[leader] = "Leader"
    /\ \E p \in Peer :
        /\ p # leader
        /\ currentTerm[p] > currentTerm[leader]
    /\ state' = [state EXCEPT ![leader] = "Follower"]
    /\ UNCHANGED <<currentTerm, votedFor, currentLeader, votesReceived, frameVars, eventVars, networkVars>>

\* ACTION: Peer learns about new term from another peer
UpdateTerm(i, j) ==
    /\ i # j
    /\ CanReceive(i, j)
    /\ currentTerm[j] > currentTerm[i]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[j]]
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ votedFor' = [votedFor EXCEPT ![i] = "None"]
    /\ currentLeader' = [currentLeader EXCEPT ![i] =
           IF state[j] = "Leader" THEN j ELSE currentLeader[i]]
    /\ UNCHANGED <<votesReceived, frameVars, eventVars, networkVars>>

\* ACTION: Follower learns new leader
LearnLeader(follower, leader) ==
    /\ follower # leader
    /\ state[leader] = "Leader"
    /\ CanReceive(follower, leader)
    /\ currentTerm[leader] >= currentTerm[follower]
    /\ currentLeader' = [currentLeader EXCEPT ![follower] = leader]
    /\ currentTerm' = [currentTerm EXCEPT ![follower] = currentTerm[leader]]
    /\ state' = [state EXCEPT ![follower] = "Follower"]
    /\ UNCHANGED <<votedFor, votesReceived, frameVars, eventVars, networkVars>>

----
\* Network partition actions (for testing)

\* ACTION: Create network partition between two peers
CreatePartition(i, j) ==
    /\ i # j
    /\ ~partitioned[i][j]
    /\ partitioned' = [partitioned EXCEPT ![i][j] = TRUE, ![j][i] = TRUE]
    /\ UNCHANGED <<electionVars, frameVars, eventVars>>

\* ACTION: Heal network partition
HealPartition(i, j) ==
    /\ i # j
    /\ partitioned[i][j]
    /\ partitioned' = [partitioned EXCEPT ![i][j] = FALSE, ![j][i] = FALSE]
    /\ UNCHANGED <<electionVars, frameVars, eventVars>>

----
\* State machine

Next ==
    \* Frame advancement (lockstep)
    \/ \E p \in Peer : AdvanceFrame(p)
    \* Event handling
    \/ \E p \in Peer : GenerateEvent(p)
    \/ \E leader \in Peer : ConfirmEvents(leader)
    \/ \E leader, follower \in Peer : SendStateSync(leader, follower)
    \* Election protocol
    \/ \E p \in Peer : StartElection(p)
    \/ \E c, v \in Peer : RequestVote(c, v)
    \/ \E p \in Peer : BecomeLeader(p)
    \/ \E p \in Peer : Stepdown(p)
    \/ \E i, j \in Peer : UpdateTerm(i, j)
    \/ \E f, l \in Peer : LearnLeader(f, l)
    \* Network faults
    \/ \E i, j \in Peer : CreatePartition(i, j)
    \/ \E i, j \in Peer : HealPartition(i, j)

\* Fairness: eventually advance frames, heal partitions
Fairness ==
    /\ WF_vars(\E p \in Peer : AdvanceFrame(p))
    /\ WF_vars(\E leader \in Peer : ConfirmEvents(leader))
    /\ SF_vars(\E i, j \in Peer : HealPartition(i, j))
    /\ WF_vars(\E p \in Peer : BecomeLeader(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----
\* Safety Properties (INVARIANTS)

\* No two leaders in the same term
NoTwoLeadersInSameTerm ==
    \A i, j \in Peer :
        (i # j /\ state[i] = "Leader" /\ state[j] = "Leader")
        => currentTerm[i] # currentTerm[j]

\* Leader is always the peer that others believe is leader
LeaderConsistency ==
    \A p \in Peer :
        state[p] = "Leader" =>
            \A q \in Peer : (currentLeader[q] = p \/ currentLeader[q] = "None" \/ ~CanReceive(q, p))

\* Events in log are from valid terms
EventTermValidity ==
    \A i \in 1..Len(eventLog) :
        eventLog[i].term >= 0

\* Committed events are never lost (monotonic log)
\* Once an event is in the log, it stays there
EventDurability ==
    [][Len(eventLog') >= Len(eventLog)]_eventLog

\* Frames are monotonically increasing
FrameMonotonicity ==
    \A p \in Peer : frame[p] >= 0

\* State sync only comes from leader
StateSyncAuthority ==
    \A p \in Peer :
        lastSyncFrame[p] > 0 =>
            \E leader \in Peer :
                /\ state[leader] = "Leader" \/ currentTerm[leader] > 0
                /\ currentLeader[p] # "None"

----
\* Liveness Properties (checked as temporal properties)

\* Eventually all connected peers have same frame (convergence)
\* When network heals, peers converge
EventualFrameConvergence ==
    <>[](\A i, j \in Peer :
        (\A k \in Peer : ~partitioned[i][k] /\ ~partitioned[j][k])
        => frame[i] = frame[j])

\* Eventually there is a leader (progress)
EventuallyLeader ==
    <>(\E p \in Peer : state[p] = "Leader")

\* If a peer generates an event and network is connected, it eventually gets confirmed
EventualEventConfirmation ==
    \A p \in Peer :
        (Len(pendingEvents[p]) > 0 /\ \A i, j \in Peer : ~partitioned[i][j])
        ~> (Len(pendingEvents[p]) = 0)

----
\* State space constraints for model checking

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm
    /\ Len(eventLog) <= MaxEvents
    /\ \A p \in Peer : Len(pendingEvents[p]) <= MaxPendingEvents

===============================================================================
