------------------------- MODULE PCRMapFilterTypes --------------------------

EXTENDS Naturals, Sequences, Functions

(* 
   Types for PCR Fib                          
*)

Null == CHOOSE x : x \notin Nat

InType1    == Seq(Nat)
VarPType1  == Nat
VarC1Type1 == BOOLEAN
VarC2Type1 == Seq(Nat\union{Null}) 
VarRType1  == Seq(Nat\union{Null}) 
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
\* Last modified Mon Nov 09 02:36:30 UYT 2020 by josedu
\* Created Sat Aug 08 21:19:28 UYT 2020 by josedu
