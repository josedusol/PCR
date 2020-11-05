------------------------------ MODULE Typedef -------------------------------

EXTENDS Naturals, Sequences, Functions

(* 
   Types for PCR Fib                          
*)

NULL == CHOOSE x : /\ x \notin Nat
                   /\ x \notin BOOLEAN
                   /\ \A R : x \notin Seq(R)

InType1    == Seq(Nat) \union {NULL}
VarPType1  == Nat \union {NULL}
VarC1Type1 == BOOLEAN \union {NULL}
VarC2Type1 == Seq(Nat\union{NULL}) \union {NULL}
VarRType1  == Seq(Nat\union{NULL}) \union {NULL}  
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

-----------------------------------------------------------------------------

SeqFoldL(seq, b, op(_,_)) ==
  LET F[s \in Seq(Range(seq))] == 
        IF s = << >> 
        THEN b 
        ELSE op(F[Tail(s)], Head(s))
  IN  F[seq]

=============================================================================
\* Modification History
\* Last modified Tue Oct 13 23:10:25 UYT 2020 by josedu
\* Created Sat Aug 08 21:19:28 UYT 2020 by josedu
