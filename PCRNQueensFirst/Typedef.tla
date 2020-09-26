------------------------------ MODULE Typedef -------------------------------

EXTENDS Integers, Sequences

(* 
   Types for PCR NQueensFirst                          
*)

Config == Seq(Nat)    

InType1    == Config
VarPType1  == Config 
VarCType1  == Config
VarRType1  == Config
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Tue Sep 22 23:44:28 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
