------------------------- MODULE PCRKaratsuba1Types -------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR Karatsuba1                          
*)

In1Type1 == Nat
In2Type1 == Nat

InType1    == In1Type1 \X In2Type1
VarPType1  == In1Type1 \X In2Type1 
VarCType1  == Nat
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

-----------------------------------------------------------------------------
           
Log(x,b) == CHOOSE n \in Nat : TRUE   \* implemented in Java        

=============================================================================
\* Modification History
\* Last modified Sat Nov 21 15:29:51 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
