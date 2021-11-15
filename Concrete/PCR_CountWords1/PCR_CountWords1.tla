-------------------------- MODULE PCR_CountWords1 --------------------------

(*
  PCR CountWords1.
   
  `.-----------------------------------------------------------------
    fun lines(Txt,i) = Txt[i]
    fun countInLine(W,l) = ...
    fun joinCounts(r,c) = r (+) c
   
    lbnd CountWords1 = \Txt, W. 1
    ubnd CountWords1 = \Txt, W. Len(Txt) 
   
    PCR CountWords1(Txt, W)  
      par
        l = produce lines Txt
        c = consume countInLine W l
        r = reduce joinCounts {{}} c
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, SeqUtils, Bags, BagUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  Concrete elements of CountWords1
*)

CONSTANT Word

Bunion == INSTANCE AbelianMonoidBigOp
  WITH D <- BagOf(Word), Id <- EmptyBag, \otimes <- (+)

T  == Seq(Seq(Word)) \X Seq(Word)
Tp == Seq(Word)
Tc == BagOf(Word)
D  == BagOf(Word)

Dep_pp == <<{},{}>>
Dep_pc == <<{},{}>>
Dep_cr == <<{},{}>>

lBnd(Txt,W) == 1
uBnd(Txt,W) == Len(Txt)
prop(i)     == TRUE

lines(Txt,i) == Txt[i]
count(l, w) == IF   w \in Range(l) 
               THEN w :> Cardinality({n \in DOMAIN l : l[n] = w})
               ELSE EmptyBag 
countInLine(W,l) == LET bs == [w \in DOMAIN W |-> count(l, W[w])]                          
                    IN  Bunion!BigOp(1, Len(bs), LAMBDA k : bs[k])  

id      == EmptyBag
Op(x,y) == x (+) y

----------------------------------------------------------------------------

(* 
  CountWords1 is a concrete instance of the abstract model PCR_A
*)

VARIABLES in, X, p, c, r, rs

I0     == <<>>
pre(x) == \A w1 \in DOMAIN x[2] :           \* Lookup Words are unique
                 ~ \E w2 \in DOMAIN x[2] : 
                         w2 # w1 /\ x[2][w1] = x[2][w2]

_lBnd(x)   == lBnd(x[1],x[2])
_uBnd(x)   == uBnd(x[1],x[2])
fp(x,vp,i) == lines(x[1],i) 
fc(x,vp,i) == countInLine(x[2],vp[i])
fr(x,vc,i) == vc[i]
gp(x,i)    == fp(x,p,i)

INSTANCE PCR_A WITH lBnd <- _lBnd, uBnd <- _uBnd

----------------------------------------------------------------------------

(* 
  Alternative correctness
*)

CountWords(Txt, W) == 
  SeqFoldL(SeqFlatten([l \in DOMAIN Txt |-> 
                         [w \in DOMAIN W |-> 
                            count(Txt[l], W[w])]]),
           EmptyBag,
           LAMBDA x,y : x (+) y)

CorrectnessAlt == end(I0) => r[I0] = CountWords(X[I0][1], X[I0][2])

=============================================================================
