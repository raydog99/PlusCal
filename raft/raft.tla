---- MODULE raft ----
(*\* Raft algorithm *)
EXTENDS Integers, Sequences, FiniteSets
CONSTANT M, N, STOP, MAXB
ASSUME M \in Nat /\ N \in Nat /\ M<=N
\* TODO: 
(*--algorithm raft
begin
end algorithm; *)
====