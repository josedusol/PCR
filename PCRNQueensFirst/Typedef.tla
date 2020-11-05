------------------------------ MODULE Typedef -------------------------------

EXTENDS Integers, Sequences

(* 
   Types for PCR NQueensFirst                          
*)

Config == Seq(Nat)   
Null   == CHOOSE x : x \notin Seq(Nat)

InType1    == Config
VarPType1  == Config 
VarCType1  == Config \union {Null}
VarRType1  == Config \union {Null}
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Fri Oct 23 15:40:55 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
