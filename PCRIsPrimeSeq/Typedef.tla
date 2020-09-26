------------------------------ MODULE Typedef -------------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR IsPrimeSeq                          
*)

InType1    == Nat
VarPType1  == Nat 
VarCType1  == BOOLEAN 
VarRType1  == BOOLEAN 
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

-----------------------------------------------------------------------------

Max(S)  == CHOOSE x \in S : \A y \in S : x >= y
Sqrt(n) == Max({ i \in Nat : i*i <= n })

=============================================================================
\* Modification History
\* Last modified Thu Sep 24 23:56:06 UYT 2020 by josedu
\* Created Sat Aug 08 21:19:28 UYT 2020 by josedu
