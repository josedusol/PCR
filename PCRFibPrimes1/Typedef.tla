------------------------------ MODULE Typedef -------------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCRFibPrimes1                          
*)

InType1    == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)
VarPType1  == Nat 
VarCType1  == BOOLEAN 
VarRType1  == Nat 

-----------------------------------------------------------------------------

Max(S)  == CHOOSE x \in S : \A y \in S : x >= y
Sqrt(n) == Max({ i \in Nat : i*i <= n })

=============================================================================
\* Modification History
\* Last modified Sun Sep 20 22:53:09 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
