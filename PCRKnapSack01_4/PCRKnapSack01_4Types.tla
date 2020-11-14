------------------------ MODULE PCRKnapSack01_4Types ------------------------

EXTENDS Integers, Sequences, SequencesExt

(* 
   Types for PCR KnapSack01_4                          
*)

Input == [n : Nat,
          w : Seq(Nat),
          v : Seq(Nat),
          C : Nat ] 
                   
Tables == LET Pos(n,m)   == {<<x, y>> : x \in 0..n, y \in 0..m}
              Table(n,m) == [Pos(n,m) -> Nat]
          IN UNION { Table(n,m) : n,m \in 0..Nat }
          
SolData == [data  : Input,
            table : Tables]           
Sol == [items  : Seq({0,1}),
        profit : Nat]   
                    
InType1      == Input
VarPType1    == SolData 
VarC1Type1   == SolData
VarC2Type1   == Seq({0,1})
VarRType1    == Sol
IndexType1   == Nat
CtxIdType1   == Seq(Nat)
IndexType1_1 == Nat 
CtxIdType1_1 == Seq(Nat)


(* 
   Types for PCR KnapSack01_4Step                          
*)

Pos == {<<x, y>> : x, y \in 0..Nat}

InType2    == SolData \X IndexType1_1
VarPType2  == Nat 
VarCType2  == [c : Pos, v : Nat]
VarRType2  == SolData
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

=============================================================================
\* Modification History
\* Last modified Wed Nov 11 18:31:45 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
