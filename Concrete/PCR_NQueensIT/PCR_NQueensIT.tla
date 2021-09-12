--------------------------- MODULE PCR_NQueensIT ---------------------------

(*
  PCR NQueensIT.
   
  `.-----------------------------------------------------------------
    fun cnd(s,j) = j > 1 and s == s[-1]
                              
    PCR NQueensIT(C)
      c1 = iterate cnd NQueensITstep {C}
        
    fun validPos(C,i,j)   = ...
    fun addQInRow(C,i)    = ... 
    fun canAddQInRow(C,i) = ...
    fun complete(C)       = all (\j. j != 0) C
    
    fun elem(CS,i) = enum(CS)[i]
    fun div(p)     = {addQInRow(p,i) | 1 <= i <= len(p), canAddQInRow(p,i)}    
    fun extend(p)  = if complete(p) then {p} else div(p) 

    lbnd NQueensITstep = \CS. 1                  
    ubnd NQueensITstep = \CS. #(CS)                  
        
    PCR NQueensITstep(CS)
      par
        p  = produce elem CS
        c2 = consume extend p
        r  = reduce union {} c2     
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, SequencesExt, FiniteSets, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  Concrete elements of NQueensIT
*)

Config == Seq(Nat)
T   == Config
Tp1 == Config
D1  == SUBSET Config

Dep_pp1 == <<{},{}>>
Dep_pc1 == <<{},{}>>
Dep_cr1 == <<{},{}>>

lBnd1(C) == 0
uBnd1(C) == 0
prop1(i) == TRUE

v0(C)    == {C}
cnd(s,j) == j > 1 /\ s[j] = s[j-1]

id1      == CHOOSE x \in D1 : TRUE
Op1(x,y) == y

(* 
  Concrete elements of NQueensITstep
*)

Tp2 == Config
Tc2 == SUBSET Config
D2  == SUBSET Config

Dep_pp2 == <<{},{}>>
Dep_pc2 == <<{},{}>>
Dep_cr2 == <<{},{}>>

lBnd2(CS) == 1
uBnd2(CS) == Cardinality(CS)
prop2(i)  == TRUE

validPos(C,i,j) == 
  /\ C[i] = 0               
  /\ \A k \in DOMAIN C : C[k] # j  
  /\ \A k \in DOMAIN C : C[k] # 0 => abs(C[k] - j) # abs(k - i)   
                                            
addQInRow(C,i)    == LET j == CHOOSE j \in DOMAIN C : validPos(C,i,j)
                     IN  [C EXCEPT ![i] = j]    
canAddQInRow(C,i) == \E j \in DOMAIN C : validPos(C,i,j)
complete(C)       == \A i \in DOMAIN C : C[i] # 0
 
elem(CS,i) == SetToSeq(CS)[i]       
div(p)     == {addQInRow(p,i) : i \in { i \in 1..Len(p) : canAddQInRow(p,i)}}                
extend(p)  == IF complete(p) THEN { p } ELSE div(p)

id2      == {}
Op2(x,y) == x \union y

----------------------------------------------------------------------------

(* 
  NQueensIT is a concrete instance of the abstract model PCR_A_it_B
*)

VARIABLES in, X1, p1, c1, s, r1, rs1,
              X2, p2, c2, r2, rs2

I0     == <<>>
pre(C) == \A i \in DOMAIN C : C[i] = 0

fp1(x1,vp,i) == x1
fr1(x1,vc,i) == vc[i]
gp1(x1,i)    == fp1(x1,p1,i)

_uBnd2(x2)   == LET CS == x2[1] IN uBnd2(CS)
fp2(x2,vp,i) == LET CS == x2[1] IN elem(CS,i) 
fc2(x2,vp,i) == extend(vp[i])
fr2(x2,vc,i) == vc[i]
gp2(x2,i)    == fp2(x2,p2,i)

INSTANCE PCR_A_it_B WITH uBnd2 <- _uBnd2

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

CorrectnessAlt == endA(I0) => r1[I0] = Solutions(X1[I0])

=============================================================================
