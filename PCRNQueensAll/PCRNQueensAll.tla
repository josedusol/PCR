-------------------------- MODULE PCRNQueensAll ----------------------------

(*
   PCR NQueensAll 
   
   ---------------------------------------------------------------------
     fun divide, isBase, base, conquer, complete, abs, canAddQueenInRow, 
         canAddQueenInCell, canAddQueens, addQueenInRow, addQueen
     
     fun iterDivide(B,j) = divide(B)[j]
     
     fun divide(B,j) = 
       cs = []
       for i in 1..Len(B)
         if canAddQueenInRow(B, i) then cs += [addQueenInRow(B, i)]
       return cs
     
     fun subproblem(B,p,j) = if   isBase(B, p, j)
                               then base(B, p, j)
                               else NQueensAll(B, p, j)
   
     fun conquer(r1,r2) = r1 union r2
   
     pre NQueensAll = \forall r \in 1..Len(B) : B[r] == 0
   
     PCR NQueensAll(B):
       par
         p = produce iterDivide B
         forall p
           c = consume subproblem B p
         r = reduce conquer [] c
   ---------------------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

abs(n) == IF n < 0 THEN -n ELSE n

\* check if queen can be placed in cell (r,c)
canAddQueenInCell(x, r, c) == 
  /\ x[r] = 0                                     \* not in same row
  /\ \A k \in DOMAIN x : x[k] # c                 \* not in same column
  /\ \A k \in DOMAIN x :                          \* not in same diagonal
        x[k] # 0 => abs(x[k] - c) # abs(k - r)

\* add queen in cell (r,c)                        
addQueen(x, r, c) == [x EXCEPT ![r] = c]                         

\* add queen in the first possible column of row r
addQueenInRow(x, r) == 
  LET N == Len(x)
      F[c \in Nat] ==
        IF c <= N
        THEN IF canAddQueenInCell(x, r, c)
             THEN addQueen(x, r, c)
             ELSE F[c+1]
        ELSE x 
  IN F[1]

\* check if queen can be placed in a row
canAddQueenInRow(x, r) == 
  LET N == Len(x)
      F[c \in Nat] ==
        IF c <= N
        THEN canAddQueenInCell(x, r, c) \/ F[c+1] 
        ELSE FALSE 
  IN F[1]      

\* check if is still possible to add queens in the unused rows
canAddQueens(x) == 
  LET N == Len(x)
      F[r \in Nat] ==
        IF r <= N
        THEN IF x[r] = 0
             THEN canAddQueenInRow(x, r) /\ F[r+1] 
             ELSE F[r+1]
        ELSE TRUE 
  IN F[1] 

\* produce further configurations where is possible to place a new queen
divide(x) == 
  LET N == Len(x)
      F[r \in Nat] ==
        IF r <= N
        THEN IF canAddQueenInRow(x, r)
             THEN <<addQueenInRow(x, r)>> \o F[r+1]
             ELSE F[r+1]
        ELSE <<>> 
  IN F[1]    

iterDivide(x, p, j) == divide(x)[j]

complete(x) == \A r \in DOMAIN x : x[r] # 0

base(x, p, j) == IF complete(p[j].v) THEN { p[j].v } ELSE {}

isBase(x, p, j) == complete(p[j].v) \/ ~ canAddQueens(p[j].v) 
 
conquer(r1, r2) == r1 \union r2

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 1
UpperBnd(x) == Len(divide(x))
Step(j)     == j + 1  

INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step

InitCtx(x) == [in  |-> x,
               i_p |-> LowerBnd(x),
               v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               ret |-> {},
               ste |-> "OFF"] 

Pre(x) == \A r \in DOMAIN x : x[r] = 0

Eureka(i) == FALSE

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall j \in 1..Len(divide(B))
            p[j] = divide B             
   
   PCR:   p = produce divide B                            
*)
P(i) == 
  \E j \in Iterator(i) : 
    /\ ~ Written(v_p(i), j)         
    /\ map' = [map EXCEPT  
         ![i].v_p[j] = [v |-> iterDivide(in(i), v_p(i), j), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(i \o <<j>>) \o " : " \o ToString(v_p(i)[j].v'))                  

(*
   Consumer non-recursive action
*)
C_base(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ isBase(in(i), v_p(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = @ + 1,
         ![i].v_c[j]   = [v |-> base(in(i), v_p(i), j), r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(i \o <<j>>) \o " : P" \o ToString(j) 
\*                       \o " con v=" \o ToString(base(in(i), v_p(i), j)))

(*
   Consumer recursive call action
*)
C_call(i) == 
  \E j \in Iterator(i):
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ isBase(in(i), v_p(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r  = 1,
         ![i \o <<j>>]  = InitCtx(v_p(i)[j].v) ]     
\*    /\ PrintT("C_call" \o ToString(i \o <<j>>) 
\*                       \o " : in= " \o ToString(in(i \o <<j>>)'))                                                                                                                                            

(*
   Consumer recursive return action
*)
C_ret(i) == 
  \E j \in Iterator(i) :
     /\ Read(v_p(i), j)       
     /\ ~ Written(v_c(i), j)
     /\ Finished(i \o <<j>>)   
     /\ map' = [map EXCEPT 
          ![i].v_c[j]= [v |-> Out(i \o <<j>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(i \o <<j>>) 
\*                       \o " : in= "  \o ToString(in(i \o <<j>>))    
\*                       \o " : ret= " \o ToString(Out(i \o <<j>>)))                

(*
   Consumer action
*)
C(i) == \/ C_base(i)
        \/ C_call(i) 
        \/ C_ret(i) 
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_c(i), j)
    /\ ~ Read(v_c(i), j)
    /\ LET ret == conquer(Out(i), v_c(i)[j].v)
           ste == CDone(i, j) \/ Eureka(ret)
       IN map' = [map EXCEPT 
           ![i].ret      = ret,
           ![i].v_c[j].r = @ + 1,
           ![i].ste      = IF ste THEN "END" ELSE @]                                                                            
\*    /\ IF State(i)' = "END"
\*       THEN PrintT("R" \o ToString(i \o <<j>>) 
\*                       \o " : in= "  \o ToString(in(i))    
\*                       \o " : ret= " \o ToString(Out(i)')) 
\*       ELSE TRUE             

Next(i) == 
  \/ /\ State(i) = "OFF" 
     /\ Start(i)
  \/ /\ State(i) = "RUN" 
     /\ \/ P(i) 
        \/ C(i) 
        \/ R(i)
        \/ Quit(i)
 
=============================================================================
\* Modification History
\* Last modified Wed Sep 23 19:00:04 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
