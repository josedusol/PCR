------------------------------ MODULE Typedef -------------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCRCountWords1                          
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
\* Last modified Sun Sep 20 20:32:15 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
