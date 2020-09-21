------------------------------ MODULE Typedef -------------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCRIsPrime                          
*)

InType1    == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat)
VarPType1  == Nat 
VarCType1  == BOOLEAN 
VarRType1  == BOOLEAN 

-----------------------------------------------------------------------------

Max(S)  == CHOOSE x \in S : \A y \in S : x >= y
Sqrt(n) == Max({ i \in Nat : i*i <= n })

=============================================================================
\* Modification History
\* Last modified Sun Sep 20 20:32:43 UYT 2020 by josedu
\* Created Sat Aug 08 21:19:28 UYT 2020 by josedu
