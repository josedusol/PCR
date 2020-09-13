------------------------------ MODULE Typedef -------------------------------

EXTENDS Naturals, Sequences

CONSTANT Elem

(* 
   Types for PCRCountWords1                          
*)
InType1    == Seq(Elem)
VarPType1  == Seq(Elem) 
VarCType1  == Seq(Elem)
VarRType1  == Seq(Elem)
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Sun Sep 13 16:37:15 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
