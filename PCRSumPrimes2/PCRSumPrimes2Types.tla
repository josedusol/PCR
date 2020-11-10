------------------------- MODULE PCRSumPrimes2Types -------------------------

EXTENDS Integers, Sequences, Functions

(* 
   Types for PCR SumPrimes2                         
*)

InType1    == Seq(Nat)
VarPType1  == Seq(Nat) 
VarCType1  == Nat
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

(* 
   Types for PCR IsPrime                          
*)

InType2    == Nat
VarPType2  == Nat 
VarCType2  == BOOLEAN 
VarRType2  == BOOLEAN 
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

-----------------------------------------------------------------------------

Max(S)  == CHOOSE x \in S : \A y \in S : x >= y
Sqrt(n) == Max({ i \in Nat : i*i <= n })

SeqFoldL(seq, b, op(_,_)) ==
  LET F[s \in Seq(Range(seq))] == 
        IF s = << >> 
        THEN b 
        ELSE op(F[Tail(s)], Head(s))
  IN  F[seq]

=============================================================================
\* Modification History
\* Last modified Tue Oct 13 00:32:23 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
