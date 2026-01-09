---- MODULE MCLockstepNetwork ----
\* Model-checking extensions for LockstepNetwork.tla

EXTENDS LockstepNetwork, TLC

MCStateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ Cardinality(network) <= MaxMessages

PeerSymmetry == Permutations(Peer \ {InitialLeader})

====
