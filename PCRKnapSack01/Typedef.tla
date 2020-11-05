------------------------------ MODULE Typedef -------------------------------

EXTENDS Integers, Sequences, SequencesExt

(* 
   Types for PCR KnapSack01                          
*)

Input == [w : Seq(Nat),
          v : Seq(Nat),
          C : Nat ]  
Row   == Seq(Nat)
Sol   == [data : Input,
          item : Nat,
          row  : Row ]              

InType1    == Input
VarPType1  == Sol 
VarCType1  == Sol
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

(* 
   Types for PCR KnapSack01Step                          
*)

InType2    == Sol
VarPType2  == Nat 
VarCType2  == [item : Nat, i : Nat, v : Nat]
VarRType2  == Sol
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Wed Nov 04 16:33:16 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
