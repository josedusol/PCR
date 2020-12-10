------------------------- MODULE PCRQuickSortTypes --------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR QuickSort                          
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
\* Last modified Tue Nov 24 01:32:11 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
