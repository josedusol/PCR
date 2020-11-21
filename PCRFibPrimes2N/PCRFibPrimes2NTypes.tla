------------------------ MODULE PCRFibPrimes2NTypes -------------------------

EXTENDS Integers, Sequences

(* 
   Types for PCR FibPrimes2N                          
*)

InType1    == Nat
VarPType1  == Nat
VarC1Type1 == BOOLEAN
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat) 

(* 
   Types for PCR IsPrime                        
*)

InType2    == Nat
VarPType2  == Nat
VarC1Type2 == BOOLEAN
VarRType2  == BOOLEAN
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

-----------------------------------------------------------------------------

Max(S)  == CHOOSE x \in S : \A y \in S : x >= y
Sqrt(n) == Max({ i \in Nat : i*i <= n })

=============================================================================
\* Modification History
\* Last modified Wed Nov 18 21:08:00 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
