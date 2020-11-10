------------------------ MODULE PCRNQueensAllITTypes ------------------------

EXTENDS Integers, Sequences, SequencesExt

(* 
   Types for PCR NQueensAllIT                          
*)

Config    == Seq(Nat)   

InType1    == Config
VarPType1  == Config 
VarCType1  == SUBSET Config
VarRType1  == SUBSET Config
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

(* 
   Types for PCR NQueensAllITStep                          
*)

InType2    == SUBSET Config
VarPType2  == Config 
VarCType2  == SUBSET Config
VarRType2  == SUBSET Config
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Tue Nov 03 22:15:02 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
