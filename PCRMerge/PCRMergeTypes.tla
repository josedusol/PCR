--------------------------- MODULE PCRMergeTypes ----------------------------

EXTENDS Integers, Sequences

(* 
   Types for PCR Merge                         
*)

CONSTANT Elem

In1Type1 == Seq(Elem)
In2Type1 == Seq(Elem)

InType1    == In1Type1 \X In2Type1
VarPType1  == In1Type1 \X In2Type1
VarCType1  == Seq(Elem)
VarRType1  == Seq(Elem)
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Tue Nov 17 18:53:24 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
