------------------------ MODULE PCRFibPrimes1NTypes -------------------------

EXTENDS Integers, Sequences

(* 
   Types for PCR FibPrimes1N                          
*)

InType1    == Nat
VarPType1  == Nat
VarC1Type1 == BOOLEAN
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)
                  
-----------------------------------------------------------------------------

Max(S)  == CHOOSE x \in S : \A y \in S : x >= y
Sqrt(n) == Max({ i \in Nat : i*i <= n })

=============================================================================
\* Modification History
\* Last modified Thu Nov 19 17:06:33 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
