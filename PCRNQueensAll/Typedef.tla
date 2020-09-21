------------------------------ MODULE Typedef -------------------------------

EXTENDS Integers, Sequences

(* 
   Types for PCRNQueensAll                          
*)

Config == Seq(Nat)    
SolSet == SUBSET Config

InType1    == Config
VarPType1  == Config 
VarCType1  == SolSet
VarRType1  == SolSet
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Sun Sep 20 20:31:49 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
