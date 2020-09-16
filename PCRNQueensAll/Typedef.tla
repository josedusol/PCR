------------------------------ MODULE Typedef -------------------------------

EXTENDS Integers, Sequences

(* 
   Types for PCRCountWords1                          
*)
Size == Nat
Sol == [Size\{0} -> Size]
Board == [sol : Sol, 
          i   : Size,
          j   : Size]         
SolSet == SUBSET Sol

InType1    == Board
VarPType1  == Board 
VarCType1  == SolSet
VarRType1  == SolSet
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Wed Sep 16 15:54:03 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
