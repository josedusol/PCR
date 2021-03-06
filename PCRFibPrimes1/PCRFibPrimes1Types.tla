------------------------- MODULE PCRFibPrimes1Types -------------------------

EXTENDS Integers, Sequences

(* 
   Types for PCR FibPrimes1                          
*)

InType1    == Nat
VarPType1  == Nat
VarCType1  == BOOLEAN
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)   
                  
-----------------------------------------------------------------------------

Max(S)  == CHOOSE x \in S : \A y \in S : x >= y
Sqrt(n) == Max({ i \in Nat : i*i <= n })

=============================================================================
\* Modification History
\* Last modified Fri Nov 06 14:39:27 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
