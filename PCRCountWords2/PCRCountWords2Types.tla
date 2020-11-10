------------------------ MODULE PCRCountWords2Types -------------------------

EXTENDS Naturals, Sequences, Bags

(* 
   Types for PCR CountWords2                          
*)

CONSTANT Word

LType == Seq(Word)
TType == Seq(LType)
WType == Seq(Word)
BagOf(S) == UNION {[xs -> Nat\{0}] : xs \in SUBSET S} \* The collection of all bags over S

InType1    == TType \X WType
VarPType1  == LType 
VarCType1  == BagOf(Word) 
VarRType1  == BagOf(Word)
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

(* 
   Types for PCR CountWordsInLine                          
*)

InType2    == LType \X WType
VarPType2  == Word 
VarCType2  == BagOf(Word) 
VarRType2  == BagOf(Word) 
IndexType2 == Nat
CtxIdType2 == Seq(Nat)

-----------------------------------------------------------------------------

Fold(seq, b, op(_,_)) ==
  LET F[s \in Seq(Range(seq))] == 
        IF s = << >> 
        THEN b 
        ELSE op(Head(s), F[Tail(s)])
  IN  F[seq]
           
Flatten(seq) == 
  LET F[s \in Seq(Range(seq))] == 
        IF s = <<>>
        THEN <<>>
        ELSE Head(s) \o F[Tail(s)]    
  IN  F[seq]
                
=============================================================================
\* Modification History
\* Last modified Tue Sep 22 23:45:33 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
