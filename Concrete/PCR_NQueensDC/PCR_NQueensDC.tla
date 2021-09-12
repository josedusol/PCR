--------------------------- MODULE PCR_NQueensDC ---------------------------

(*
  PCR NQueensDC.
   
  `.-----------------------------------------------------------------
    fun validPos(C,i,j)   = ...
    fun addQInRow(C,i)    = ... 
    fun canAddQInRow(C,i) = ...
    fun canAddQueens(C)   = ... 
    fun complete(C)       = all (\j. j != 0) C
    
    fun div(C)    = [addQInRow(C,i) | 1 <= i <= len(C), canAddQInRow(C,i)]
    fun isBase(p) = complete(p) or not canAddQueens(p)
    fun base(p)   = if complete(p) then { p } else {}  
                              
    PCR NQueensDC(C)
      par
        p = produce iterDiv C
        c = consume subproblem C p
        r = reduce union {} c
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, SeqUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  Concrete elements of NQueensDC
*)

Config == Seq(Nat)
T == SUBSET Config
D == SUBSET Config

Dep_pc == <<{},{}>>
Dep_cr == <<{},{}>>

validPos(C,i,j) == 
  /\ C[i] = 0               
  /\ \A k \in DOMAIN C : C[k] # j  
  /\ \A k \in DOMAIN C : C[k] # 0 => abs(C[k] - j) # abs(k - i)   
                                            
addQInRow(C,i)    == LET j == CHOOSE j \in DOMAIN C : validPos(C,i,j)
                     IN  [C EXCEPT ![i] = j]    
canAddQInRow(C,i) == \E j \in DOMAIN C : validPos(C,i,j)
canAddQueens(C)   == \A i \in DOMAIN C : C[i] = 0 => canAddQInRow(C,i)
complete(C)       == \A i \in DOMAIN C : C[i] # 0

div(C)    == Map(LAMBDA i : addQInRow(C,i), 
                 SelectSeq(1...Len(C), LAMBDA i : canAddQInRow(C,i)))
isBase(p) == complete(p) \/ ~ canAddQueens(p)           
base(p)   == IF complete(p) THEN { p } ELSE {}

id      == {}
Op(x,y) == x \union y

----------------------------------------------------------------------------

(* 
  NQueensDC is a concrete instance of the abstract model PCR_DC
*)

VARIABLES in, X, p, c, r, rs

I0     == <<>>
pre(C) == \A i \in DOMAIN C : C[i] = 0

_base(x,vp,i)   == base(vp[i])
_isBase(x,vp,i) == isBase(vp[i])
fr(x,vc,i)      == vc[i]

INSTANCE PCR_DC WITH base <- _base, isBase <- _isBase

----------------------------------------------------------------------------

(* 
  Alternative correctness
*)

Solutions(x) == CASE Len(x) = 0      -> { }
                  [] Len(x) = 1      -> { <<1>> }
                  [] Len(x) \in 2..3 -> { }
                  [] Len(x) = 4      -> { <<3,1,4,2>>, 
                                          <<2,4,1,3>> }
                  [] Len(x) = 5      -> { <<1, 3, 5, 2, 4>>,  
                                          <<1, 4, 2, 5, 3>>,
                                          <<2, 4, 1, 3, 5>>,
                                          <<2, 5, 3, 1, 4>>,
                                          <<3, 1, 4, 2, 5>>,
                                          <<3, 5, 2, 4, 1>>,                                         
                                          <<4, 1, 3, 5, 2>>,
                                          <<4, 2, 5, 3, 1>>, 
                                          <<5, 2, 4, 1, 3>>,
                                          <<5, 3, 1, 4, 2>> }
                  [] Len(x) = 6      -> { <<2, 4, 6, 1, 3, 5>>, 
                                          <<3, 6, 2, 5, 1, 4>>, 
                                          <<4, 1, 5, 2, 6, 3>>, 
                                          <<5, 3, 1, 6, 4, 2>> }
                  [] Len(x) > 6      -> "ask google..."                        

CorrectnessAlt == end(I0) => r[I0] = Solutions(X[I0])

=============================================================================
