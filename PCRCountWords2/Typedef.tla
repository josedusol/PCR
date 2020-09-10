------------------------------ MODULE Typedef -------------------------------

EXTENDS Naturals, Sequences, Bags

Word  == Nat
LType == Seq(Word)
TType == Seq(LType)
WType == Seq(Word)
BagOf(S) == UNION {[xs -> Nat\{0}] : xs \in SUBSET S} \* The collection of all bags over S

(* 
   Types for PCRCountWords2                          
*)
InType1    == TType \X WType
VarPType1  == LType 
VarCType1  == BagOf(Word) 
VarRType1  == BagOf(Word)
IndexType1 == Nat\{0}
CtxIdType1 == Seq(Nat)

(* 
   Types for PCRCountWordsInLine                          
*)
InType2    == LType \X WType
VarPType2  == Word 
VarCType2  == BagOf(Word) 
VarRType2  == BagOf(Word) 
IndexType2 == Nat\{0}
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
\* Last modified Wed Sep 09 19:58:37 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
