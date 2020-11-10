----------------------- MODULE PCRNQueensFirstITTypes -----------------------

EXTENDS Integers, Sequences, SequencesExt

(* 
   Types for PCR NQueensFirstIT                          
*)

Config    == Seq(Nat)   

InType1    == Config
VarPType1  == Config 
VarCType1  == SUBSET Config
VarRType1  == SUBSET Config
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

(* 
   Types for PCR NQueensFirstITStep                          
*)

InType2    == SUBSET Config
VarPType2  == Config 
VarCType2  == SUBSET Config
VarRType2  == SUBSET Config
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 21:22:32 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
