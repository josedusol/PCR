------------------------------ MODULE Typedef -------------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR FibPrimes5                          
*)

InType1    == Nat
VarPType1  == Nat 
VarCType1  == BOOLEAN 
VarRType1  == Nat
IndexType1 == Nat
CtxIdType1 == Seq(Nat) 

(* 
   Types for PCR FibRec                          
*)

InType2    == Nat
VarPType2  == Nat 
VarCType2  == Nat 
VarRType2  == Nat 
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

-----------------------------------------------------------------------------

Max(S)  == CHOOSE x \in S : \A y \in S : x >= y
Sqrt(n) == Max({ i \in Nat : i*i <= n })

=============================================================================
\* Modification History
\* Last modified Fri Sep 25 02:15:02 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
