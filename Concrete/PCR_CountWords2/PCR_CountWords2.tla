-------------------------- MODULE PCR_CountWords2 --------------------------

(*
  PCR CountWords2.
   
  `.-----------------------------------------------------------------
    fun lines(Txt,i) = Txt[i]
    fun joinCounts(r,c) = r (+) c
   
    lbnd CountWords2 = \Txt, W. 1
    ubnd CountWords2 = \Txt, W. Len(Txt) 
   
    PCR CountWords2(Txt, W)  
      par
        l  = produce lines Txt
        c1 = consume countInLine W l
        r1 = reduce joinCounts {{}} c1
        
    fun words(W,i) = W[i]    
    fun count(L,w) = ...
        
    lbnd CountInLine = \W, L. 1
    ubnd CountInLine = \W, L. Len(W)         
        
    PCR CountInLine(W, L)      
      par
        w  = produce words W
        c2 = consume count L w
        r2 = reduce joinCounts {{}} c2
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, SeqUtils, Bags, BagUtils, ArithUtils, TLC

----------------------------------------------------------------------------

CONSTANT Word

Bunion == INSTANCE AbelianMonoidBigOp
  WITH D <- BagOf(Word), Id <- EmptyBag, \otimes <- (+)

(* 
  Concrete elements of CountWords2
*)

T   == Seq(Seq(Word)) \X Seq(Word)
Tp1 == Seq(Word)
Tc1 == BagOf(Word)
D1  == BagOf(Word)

Dep_pp1 == <<{},{}>>
Dep_pc1 == <<{},{}>>
Dep_cr1 == <<{},{}>>

lBnd1(Txt,W) == 1
uBnd1(Txt,W) == Len(Txt)
prop1(i)     == TRUE

lines(Txt,i) == Txt[i]

id1      == EmptyBag
Op1(x,y) == x (+) y

(* 
  Concrete elements of CountInLine
*)

Tp2 == Word
Tc2 == BagOf(Word)
D2  == BagOf(Word)

Dep_pp2 == <<{},{}>>
Dep_pc2 == <<{},{}>>
Dep_cr2 == <<{},{}>>

lBnd2(W,L) == 1
uBnd2(W,L) == Len(W)
prop2(i)   == TRUE

words(W,i) == W[i]
count(L,w) == IF   w \in Range(L) 
              THEN w :> Cardinality({n \in DOMAIN L : L[n] = w})
              ELSE EmptyBag

id2      == EmptyBag
Op2(x,y) == x (+) y

----------------------------------------------------------------------------

(* 
  CountWords2 is a concrete instance of the abstract model PCR_A_c_B
*)

VARIABLES in, X1, p1, c1, r1, rs1,
              X2, p2, c2, r2, rs2

I0     == <<>>
pre(x) == \A w1 \in DOMAIN x[2] :           \* Lookup Words are unique
                 ~ \E w2 \in DOMAIN x[2] : 
                         w2 # w1 /\ x[2][w1] = x[2][w2]

_lBnd1(x1)   == lBnd1(x1[1],x1[2])
_uBnd1(x1)   == uBnd1(x1[1],x1[2])
fp1(x1,vp,i) == lines(x1[1],i) 
fr1(x1,vc,i) == vc[i]
gp1(x1,i)    == fp1(x1,p1,i)

_lBnd2(x2)   == LET W == x2[1][2]
                    L == x2[2][x2[3]] IN lBnd2(W,L) 
_uBnd2(x2)   == LET W == x2[1][2] 
                    L == x2[2][x2[3]] IN uBnd2(W,L) 
fp2(x2,vp,i) == LET W == x2[1][2] IN words(W, i) 
fc2(x2,vp,i) == LET L == x2[2][x2[3]] IN count(L,vp[i])
fr2(x2,vc,i) == vc[i]
gp2(x2,i)    == fp2(x2,p2,i)

INSTANCE PCR_A_c_B WITH lBnd1 <- _lBnd1, uBnd1 <- _uBnd1,
                        lBnd2 <- _lBnd2, uBnd2 <- _uBnd2  

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

CorrectnessAlt == endA(I0) => r1[I0] = CountWords(X1[I0][1], X1[I0][2])

=============================================================================
