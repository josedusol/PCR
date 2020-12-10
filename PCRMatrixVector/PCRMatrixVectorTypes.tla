------------------------ MODULE PCRMatrixVectorTypes ------------------------

EXTENDS Integers, Sequences, FiniteSets

(* 
   Types for PCR MatrixVector                          
*)

Matrix == LET Pos(n,m) == {<<x, y>> : x \in 0..n, y \in 0..m}
              Mtx(n)   == [Pos(n,n) -> Nat]
          IN UNION { Mtx(n) : n \in Nat }
Vector == Seq(Nat)

In1Type1 == Nat
In2Type1 == Matrix
In3Type1 == Vector
        
InType1      == In1Type1 \X In2Type1 \X In3Type1
VarPType1    == Nat
VarCType1    == Nat
VarRType1    == Vector
IndexType1   == Nat
CtxIdType1   == Seq(Nat)
IndexType1_1 == Nat 
CtxIdType1_1 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Tue Nov 24 23:36:35 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
