------------------------------ MODULE Raft ------------------------------

EXTENDS Integers, TLC

\* Constants and variables
CONSTANT N \* Number of nodes
CONSTANT Value \* Set of possible values

\* Variables
VARIABLE state \* State of each node
VARIABLE currentTerm \* Current term number
VARIABLE votedFor \* Candidate that received vote in current term
VARIABLE log \* Log entries

\* Constants
InitState == [role |-> "follower", commitIndex |-> 0, lastApplied |-> 0]

\* Init predicate
Init ==
    /\ state \in [1..N -> InitState]
    /\ currentTerm = 0
    /\ votedFor = NULL
    /\ log = <<>>

\* Algorithm steps

\* Phase 1: Elections

RequestVote(p, term, lastLogIndex, lastLogTerm) ==
    /\ state[p].role \in {"follower", "candidate"}
    /\ IF term > currentTerm
       THEN /\ currentTerm' = term
             /\ state' = [state EXCEPT ![p].role = "follower"]
       ELSE /\ UNCHANGED currentTerm
    /\ LET voteGranted == (votedFor = NULL \/ (term = currentTerm /\ votedFor = p))
       IN /\ IF term >= currentTerm /\ lastLogIndex >= Len(log) /\ lastLogTerm >= log[Len(log)][2]
             THEN /\ votedFor' = p
                   /\ state' = [state EXCEPT ![p].role = "follower"]
                   /\ voteGranted
             ELSE /\ voteGranted

\* Phase 2: Leader election

StartElection(p, term) ==
    /\ state[p].role = "candidate"
    /\ currentTerm' = term
    /\ state' = [state EXCEPT ![p].role = "candidate"]
    /\ votedFor' = p

\* Phase 3: Log replication

AppendEntries(p, term, prevLogIndex, prevLogTerm, entries, leaderCommit) ==
    /\ state[p].role \in {"follower", "candidate", "leader"}
    /\ IF term >= currentTerm
       THEN /\ currentTerm' = term
             /\ state' = [state EXCEPT ![p].role = "follower"]
             /\ votedFor' = NULL
       ELSE /\ UNCHANGED currentTerm
    /\ LET logMatch == (prevLogIndex = 0 \/ (prevLogIndex < Len(log) /\ log[prevLogIndex][2] = prevLogTerm))
       IN /\ IF term >= currentTerm /\ logMatch
             THEN /\ log' = AppendEntriesToLog(log, prevLogIndex, entries)
                   /\ state' = [state EXCEPT ![p].commitIndex = leaderCommit]
                   /\ TRUE
             ELSE /\ FALSE

AppendEntriesToLog(log, prevLogIndex, entries) ==
    /\ IF prevLogIndex + 1 = Len(log) /\ entries # <<>>
       THEN log \o entries
       ELSE IF prevLogIndex + 1 <= Len(log) /\ log[prevLogIndex + 1] = entries[1]
              THEN AppendEntriesToLog(log, prevLogIndex + 1, Tail(entries))
              ELSE log

\* Phase 4: State machine execution

ApplyStateMachine(p) ==
    /\ state[p].role \in {"follower", "candidate", "leader"}
    /\ LET lastLogIndex == Len(log)
           entries == log[state[p].commitIndex + 1 .. lastLogIndex]
       IN /\ state' = [state EXCEPT ![p].lastApplied = lastLogIndex]

\* Next state relation
Next ==
    \E p \in 1..N :
        \/ \E term \in Nat, lastLogIndex \in Nat, lastLogTerm \in Nat :
               RequestVote(p, term, lastLogIndex, lastLogTerm)
        \/ \E term \in Nat :
               StartElection(p, term)
        \/ \E term \in Nat, prevLogIndex \in Nat, prevLogTerm \in Nat, entries \in Seq(Value), leaderCommit \in Nat :
               AppendEntries(p, term, prevLogIndex, prevLogTerm, entries, leaderCommit)
        \/ ApplyStateMachine(p)

\* Safety properties

\* Election safety: At most one leader per term
ElectionSafety ==
    \A p, q \in 1..N : state[p].role = "leader" /\ state[q].role = "leader" => currentTerm[p] = currentTerm[q]

\* Log matching: Logs of different nodes must be identical in the beginning
LogMatching ==
    \A p, q \in 1..N :
        \A i \in 1..Len(log) : log[p][i][2] = log[q][i][2]

\* Liveness properties

\* Election completeness: Eventually, a leader is elected
ElectionCompleteness ==
    \A p \in 1..N : <>(state[p].role = "leader")

\* Combined specification
Spec == Init /\ [][Next]_state

\* Properties to check
Properties == ElectionSafety /\ LogMatching /\ ElectionCompleteness

=============================================================================