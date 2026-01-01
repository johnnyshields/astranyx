---- MODULE MCLockstepSimple ----
\* Model-checking extensions for LockstepSimple.tla

EXTENDS LockstepSimple, TLC

MCStateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm

PeerSymmetry == Permutations(Peer)

====
