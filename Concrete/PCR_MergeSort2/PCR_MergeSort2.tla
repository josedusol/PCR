--------------------------- MODULE PCR_MergeSort2 ---------------------------

(*
  PCR MergeSort2.
   
  `.-----------------------------------------------------------------
    fun div1(L)    = let m = floor(len(L) / 2)
                     in [L[1..m], L[m+1..len(L)]]
    fun isBase1(p) = len(p) <= 1 
    fun base1(p)   = p   
                              
    PCR MergeSort2(L)
      par
        p1 = produce iterDiv1 L
        c1 = consume subproblem1 L p1
        r1 = reduce Merge [] c1

    fun binarySearch(L,e) = ...
    fun div2(L1,L2) = [(L11,L21), (L21,L22)]    // ensure len(L1) >= len(L2) 
                      where m   = floor(len(L1) / 2)
                            L11 = L1[1..m]
                            L12 = L1[m+1..len(L1)]
                            k   = binarySearch(L2, L12[1])
                            L21 = L2[1..k]
                            L22 = L2[k+1..len(L2)]                             
    fun isBase2(p) = len(p[1]) <= 1 and len(p[2]) <= 1
    fun base2(p)   = merge(p[1],p[2])  
                              
    PCR Merge(L1, L2)
      par
        p2 = produce iterDiv2 L1 L2
        c2 = consume subproblem2 L1 L2 p2
        r2 = reduce ++ [] c2
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, SeqUtils, ArithUtils, TLC

-----------------------------------------------------------------------------

(* 
  Concrete elements of MergeSort2
*)

CONSTANT Elem

T == Seq(Elem)
D == Seq(Elem)

Dep_pc1 == <<{},{}>>
Dep_cr1 == <<{},{}>>

div1(L)    == LET mid == Len(L) \div 2
              IN  << SubSeq(L,1,mid), SubSeq(L,mid+1,Len(L)) >>
isBase1(p) == Len(p) <= 1              
base1(p)   == p

id == <<>>

(* 
  Concrete elements of Merge
*)

Dep_pc2 == <<{},{}>>
Dep_cr2 == <<{},{}>>

binarySearch(seq, e) ==
  LET f[s \in Seq(Elem)] == 
    IF s = <<>> THEN 0
    ELSE LET m == (Len(s)+1) \div 2
         IN  CASE e = s[m] -> m
               [] e < s[m] -> f[SubSeq(s, 1, m-1)]
               [] e > s[m] -> LET pv == f[SubSeq(s,m+1,Len(s))]
                              IN  IF pv > 0 THEN pv+m+1 ELSE m-pv
  IN f[seq]

div2(_L1,_L2) ==                                \* Make sure len(L1) >= len(L2)
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
     
isBase2(p) == Len(p[1]) <= 1 /\ Len(p[2]) <= 1         
base2(p)   == p[1] \uplus p[2]

Op2(x,y) == x \o y

-----------------------------------------------------------------------------

(* 
  MergeSort2 is a concrete instance of the abstract model PCR_DC_r_DCrLeft
*)

VARIABLES in, X1, p1, c1, r1, rs1,
              X2, p2, c2, r2, rs2

I0     == <<>>
pre(x) == TRUE

_div1(x)         == div1(x)
_base1(x,vp,i)   == base1(vp[i])
_isBase1(x,vp,i) == isBase1(vp[i])
fr1(x,vc,i)      == vc[i]

_div2(x)         == div2(x[1],x[2])
_base2(x,vp,i)   == base2(vp[i])
_isBase2(x,vp,i) == isBase2(vp[i])
fr2(x,vc,i)      == vc[i]

INSTANCE PCR_DC_r_DCrLeft 
  WITH div1 <- _div1, base1 <- _base1, isBase1 <- _isBase1,
       div2 <- _div2, base2 <- _base2, isBase2 <- _isBase2

-----------------------------------------------------------------------------

(* 
  Alternative correctness
*)

CorrectnessAlt == endA(I0) => r1[I0] = SortSeq(X1[I0], <)

============================================================================-
