---- MODULE MCLockstepNetwork ----
\* Model-checking extensions for LockstepNetwork.tla

EXTENDS LockstepNetwork, TLC

MCStateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : Cardinality(pendingEvents[p]) <= MaxEvents
    /\ Cardinality(network) <= MaxMessages

PeerSymmetry == Permutations(Peer)

====
