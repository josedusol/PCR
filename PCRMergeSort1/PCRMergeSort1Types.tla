------------------------- MODULE PCRMergeSort1Types -------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR MergeSort1               
*)

CONSTANT Elem

InType1    == Seq(Elem)
VarPType1  == Seq(Elem) 
VarCType1  == Seq(Elem)
VarRType1  == Seq(Elem)
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Thu Nov 12 21:24:37 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
