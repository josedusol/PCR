------------------------ MODULE PCRKnapSack01_3Types ------------------------

EXTENDS Integers, Sequences, SequencesExt

(* 
   Types for PCR KnapSack01_3                          
*)

Input == [n : Nat,
          w : Seq(Nat),
          v : Seq(Nat),
          C : Nat ]  
Row   == Seq(Nat)
Sol   == [data : Input,
          row  : Row ]           
                    
InType1    == Input
VarPType1  == Sol 
VarCType1  == Sol
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)


(* 
   Types for PCR KnapSack01_3Iterate                        
*)

InType2    == Sol
VarPType2  == Sol 
VarCType2  == Sol
VarRType2  == Sol
IndexType2 == Nat
CtxIdType2 == Seq(Nat)


(* 
   Types for PCR KnapSack01_3Step                          
*)

InType3    == Sol \X IndexType2
VarPType3  == Nat 
VarCType3  == [j : Nat, v : Nat]
VarRType3  == Sol
IndexType3 == Nat
CtxIdType3 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Fri Nov 13 00:37:52 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
