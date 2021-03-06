------------------------- MODULE PCRKaratsuba2Types -------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR Karatsuba2                  
*)

In1Type1 == Nat
In2Type1 == Nat

InType1    == In1Type1 \X In2Type1
VarPType1  == In1Type1 \X In2Type1 
VarC1Type1 == Nat
VarC2Type1 == Nat
VarC3Type1 == Nat
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

-----------------------------------------------------------------------------
           
Log(x,b) == CHOOSE n \in Nat : TRUE   \* implemented in Java        

=============================================================================
\* Modification History
\* Last modified Fri Dec 11 15:59:08 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
