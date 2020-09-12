------------------------------ MODULE Typedef -------------------------------

EXTENDS Naturals, Sequences, Bags

Word  == STRING
LType == Seq(Word)
WType == Seq(Word)
BagOf(S) == UNION {[xs -> Nat\{0}] : xs \in SUBSET S} \* The collection of all bags over S

InType1    == LType \X WType
VarPType1  == Word
VarCType1  == BagOf(Word) 
VarRType1  == BagOf(Word)
IndexType1 == Nat
CtxIdType1 == Seq(Nat)

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
\* Last modified Sat Sep 12 17:36:03 UYT 2020 by josedu
\* Created Fri Aug 07 14:29:49 UYT 2020 by josedu
