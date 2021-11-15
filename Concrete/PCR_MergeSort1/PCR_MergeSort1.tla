------------------------ MODULE PCR_MergeSort1 -----------------------------

(*
  PCR MergeSort1.
   
  `.-----------------------------------------------------------------
    fun div(L)    = let m = floor(len(L) / 2)
                    in [L[1..m], L[m+1..len(L)]]
    fun isBase(p) = len(p) <= 1 
    fun base(p)   = p   
                              
    PCR MergeSort1(L)
      par
        p = produce iterDiv L
        c = consume subproblem L p
        r = reduce merge [] c
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, SeqUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  Concrete elements of MergeSort1
*)

CONSTANT Elem

T == Seq(Elem)
D == Seq(Elem)

Dep_pc == <<{},{}>>
Dep_cr == <<{},{}>>

div(L)    == LET mid == Len(L) \div 2
             IN  << SubSeq(L,1,mid), SubSeq(L,mid+1,Len(L)) >>
isBase(p) == Len(p) <= 1              
base(p)   == p

id      == <<>>
Op(x,y) == x \uplus y

----------------------------------------------------------------------------

(* 
  MergeSort1 is a concrete instance of the abstract model PCR_DC
*)

VARIABLES in, X, p, c, r, rs

I0     == <<>>
pre(x) == TRUE

_base(x,vp,i)   == base(vp[i])
_isBase(x,vp,i) == isBase(vp[i])
fr(x,vc,i)      == vc[i]

INSTANCE PCR_DC WITH base <- _base, isBase <- _isBase

----------------------------------------------------------------------------

(* 
  Alternative correctness
*)

CorrectnessAlt == end(I0) => r[I0] = SortSeq(X[I0], <)

=============================================================================