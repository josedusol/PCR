------------------------- MODULE PCRFirstEvenTypes --------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR FirstEven                          
*)

Null == CHOOSE x : x \notin Nat

InType1    == Nat
VarPType1  == Nat 
VarCType1  == Nat \union {Null} 
VarRType1  == Nat \union {Null} 
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 01:41:02 UYT 2020 by josedu
\* Created Sat Aug 08 21:19:28 UYT 2020 by josedu
