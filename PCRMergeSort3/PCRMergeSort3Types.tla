-------------------------- MODULE PCRMergeSort3Types ------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR MergeSort3                          
*)

CONSTANT Elem

InType1    == Seq(Elem)
VarPType1  == Seq(Elem) 
VarC1Type1 == Seq(Elem)
VarC2Type1 == Seq(Elem)
VarRType1  == Seq(Elem)
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

(* 
   Types for PCR Merge                      
*)

In1Type2 == Seq(Elem)
In2Type2 == Seq(Elem)

InType2    == In1Type2 \X In2Type2
VarPType2  == In1Type2 \X In2Type2
VarCType2  == Seq(Elem)
VarRType2  == Seq(Elem)
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Sun Nov 22 22:27:13 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
