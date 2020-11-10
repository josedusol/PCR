----------------------- MODULE PCRNQueensAllDCTypes -------------------------

EXTENDS Integers, Sequences

(* 
   Types for PCR NQueensAllDC                          
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
\* Last modified Tue Sep 22 23:44:19 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
