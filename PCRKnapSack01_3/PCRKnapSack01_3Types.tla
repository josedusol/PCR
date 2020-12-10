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
                    
InType1    == Input
VarPType1  == Row 
VarCType1  == Row
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)


(* 
   Types for PCR KnapSack01_2Iterate                        
*)

InType2    == Input \X Row
VarPType2  == Row 
VarCType2  == Row
VarRType2  == Row
IndexType2 == Nat
CtxIdType2 == Seq(Nat)


(* 
   Types for PCR KnapSack01_2Step                          
*)

InType3    == Input \X Row \X IndexType2
VarPType3  == InType3 
VarCType3  == Nat
VarRType3  == Row
IndexType3 == Nat
CtxIdType3 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Wed Nov 25 15:43:34 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
