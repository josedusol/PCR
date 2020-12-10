------------------------ MODULE PCRKnapSack01_4Types ------------------------

EXTENDS Integers, Sequences, SequencesExt

(* 
   Types for PCR KnapSack01_4                          
*)

Input == [n : Nat,
          w : Seq(Nat),
          v : Seq(Nat),
          C : Nat ] 
                   
Table == LET Pos(n,m) == {<<x, y>> : x \in 0..n, y \in 0..m}
             Tab(n,m) == [Pos(n,m) -> Nat]
         IN UNION { Tab(n,m) : n,m \in Nat }
          
\*SolData == [data  : Input,
\*            table : Table]           
Sol == [items  : Seq({0,1}),
        profit : Nat]   
                    
InType1      == Input
VarPType1    == Table 
VarC1Type1   == Table
VarC2Type1   == Seq({0,1})
VarRType1    == Sol
IndexType1   == Nat
CtxIdType1   == Seq(Nat)
IndexType1_1 == Nat 
CtxIdType1_1 == Seq(Nat)


(* 
   Types for PCR KnapSack01_4Step                          
*)

Pos == {<<x, y>> : x, y \in Nat}

InType2    == Input \X Table \X IndexType1_1
VarPType2  == Nat
VarCType2  == [c : Pos, v : Nat]
VarRType2  == Table
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Wed Nov 25 16:31:16 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
