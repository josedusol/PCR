------------------------- MODULE PCRIsPrimeRecTypes --------------------------

EXTENDS Naturals, Sequences

(* 
   Types for PCR IsPrimeRec                          
*)

In1Type1 == Nat
In2Type1 == Nat

InType1    == In1Type1 \X In2Type1
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
\* Last modified Mon Nov 09 02:04:28 UYT 2020 by josedu
\* Created Sat Aug 08 21:19:28 UYT 2020 by josedu
