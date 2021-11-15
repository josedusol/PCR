----------------------------- MODULE PCR_Merge -----------------------------

(*
  PCR Merge.
   
  `.-----------------------------------------------------------------
    fun binarySearch(L,e) = ...
    fun div(L1,L2) = [(L11,L21), (L21,L22)]    // ensure len(L1) >= len(L2) 
                     where m   = floor(len(L1) / 2)
                           L11 = L1[1..m]
                           L12 = L1[m+1..len(L1)]
                           k   = binarySearch(L2, L12[1])
                           L21 = L2[1..k]
                           L22 = L2[k+1..len(L2)]                             
    fun isBase(p) = len(p[1]) <= 1 and len(p[2]) <= 1
    fun base(p)   = merge(p[1],p[2])  
                              
    PCR Merge(L1, L2)
      par
        p = produce iterDiv L1 L2
        c = consume subproblem L1 L2 p
        r = reduce ++ [] c
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, SeqUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  Concrete elements of Merge
*)

CONSTANT Elem

T == Seq(Elem) \X Seq(Elem)
D == Seq(Elem)

Dep_pc == <<{},{}>>
Dep_cr == <<{},{}>>

binarySearch(seq, e) ==
  LET f[s \in Seq(Elem)] == 
    IF s = <<>> THEN 0
    ELSE LET m == (Len(s)+1) \div 2
         IN  CASE e = s[m] -> m
               [] e < s[m] -> f[SubSeq(s, 1, m-1)]
               [] e > s[m] -> LET pv == f[SubSeq(s,m+1,Len(s))]
                              IN  IF pv > 0 THEN pv+m+1 ELSE m-pv
  IN f[seq]

div(_L1,_L2) ==                                 \* Make sure len(L1) >= len(L2)
  LET L1 == IF Len(_L1) >= Len(_L2) THEN _L1 ELSE _L2  
      L2 == IF Len(_L1) >= Len(_L2) THEN _L2 ELSE _L1 
  IN LET m   == Len(L1) \div 2                  \* a. Split L1 in halves L11 and L12
         L11 == SubSeq(L1, 1, m) 
         L12 == SubSeq(L1, m+1, Len(L1))       
         k   == binarySearch(L2, L12[1])        \* b. Search position of L12[1] in L2
         L21 == CASE k = 0          -> << >>    \* c. Split L2 in that position
                     [] k > Len(L2) -> L2
                     [] OTHER       -> SubSeq(L2,1,k)                          
         L22 == CASE k = 0          -> L2                        
                     [] k > Len(L2) -> << >>
                     [] OTHER       -> SubSeq(L2,k+1,Len(L2))
     IN  << <<L11,L21>>, <<L12,L22>> >>         \* Produce two sub-merges
     
isBase(p) == Len(p[1]) <= 1 /\ Len(p[2]) <= 1         
base(p)   == p[1] \uplus p[2]

id      == <<>>
Op(x,y) == x \o y

----------------------------------------------------------------------------

(* 
  Merge is a concrete instance of the abstract model PCR_DCrLeft
*)

VARIABLES in, X, p, c, r, rs

I0     == <<>>
pre(x) == IsOrdered(x[1]) /\ IsOrdered(x[2])

_div(x)         == div(x[1],x[2])
_base(x,vp,i)   == base(vp[i])
_isBase(x,vp,i) == isBase(vp[i])
fr(x,vc,i)      == vc[i]

INSTANCE PCR_DCrLeft WITH div <- _div, base <- _base, isBase <- _isBase

----------------------------------------------------------------------------

(* 
  Alternative correctness
*)

CorrectnessAlt == end(I0) => r[I0] = X[I0][1] \uplus X[I0][2]

============================================================================
