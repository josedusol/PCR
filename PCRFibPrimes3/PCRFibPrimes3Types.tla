------------------------- MODULE PCRFibPrimes3Types -------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR FibPrimes3                         
*)

InType1    == Nat
VarPType1  == Nat 
VarCType1  == BOOLEAN 
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat) 

(* 
   Types for PCR IsPrimeRec                          
*)

In1Type2 == Nat
In2Type2 == Nat

InType2    == In1Type2 \X In2Type2
VarPType2  == Nat 
VarCType2  == BOOLEAN 
VarRType2  == BOOLEAN 
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

-----------------------------------------------------------------------------

Max(S)  == CHOOSE x \in S : \A y \in S : x >= y
Sqrt(n) == Max({ i \in Nat : i*i <= n })

=============================================================================
\* Modification History
\* Last modified Wed Sep 23 16:43:47 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
