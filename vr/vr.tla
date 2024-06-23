------------------------------ MODULE VR ------------------------------

EXTENDS Integers, TLC

CONSTANT N \* Number of replicas
CONSTANT Value \* Set of possible values

\* Variables
VARIABLE state \* State of each replica

\* Constants
InitState == [phase |-> "idle", view |-> 0, x |-> NULL]

\* Init predicate
Init ==
    /\ state \in [1..N -> InitState]

\* Algorithm steps

\* Phase 1: Primary proposes a value
PrimaryPhase(p) ==
    /\ state[p].phase = "idle"
    /\ LET m == CHOOSE m \in Value : TRUE
       IN state' = [state EXCEPT ![p].x = m, ![p].phase = "prepare"]

\* Phase 2: Replicas prepare and commit
ReplicaPrepare(p) ==
    /\ state[p].phase = "prepare"
    /\ LET v == state[p].view, x == state[p].x
       IN state' = [state EXCEPT ![p].phase = "commit", ![p].x = x]

\* Next state relation
Next ==
    \E p \in 1..N :
        \/ PrimaryPhase(p)
        \/ ReplicaPrepare(p)

\* Safety properties

\* Agreement: All replicas decide the same value
Agreement ==
    \A p, q \in 1..N : state[p].phase = "commit" /\ state[q].phase = "commit" => state[p].x = state[q].x

\* Liveness properties

\* Termination: All replicas eventually decide
Termination ==
    \A p \in 1..N : state[p].phase = "commit"

\* Combined specification
Spec == Init /\ [][Next]_state

\* Properties to check
Properties == Agreement /\ Termination

=============================================================================