------------------------- MODULE PCRNQueensFirst ---------------------------

(*
   PCR NQueensFirst
   
   ---------------------------------------------------------------------
     fun divide, isBase, base, conquer, complete, abs, canAddQueenInRow, 
         canAddQueenInCell, canAddQueens, addQueenInRow, addQueen
     
     fun iterDivide(B,p,i) = divide(B)[i]
     
     fun divide(B) = 
       cs = []
       for i in 1..Len(B)
         if canAddQueenInRow(B, i) then cs += [addQueenInRow(B, i)]
       return cs
     
     fun subproblem(B,p,i) = if   isBase(B, p, i)
                             then base(B, p, i)
                             else NQueensFirst(B, p, i)
   
     fun conquer(r1,r2) = r1 ++ r2
     
     cnd terminate(r) = complete(r)
     
     pre NQueensAll = \forall r \in 1..Len(B) : B[r] == 0
   
     PCR NQueensFirst(B):
       par
         p = produce iterDivide B
         forall p
           c = consume subproblem B p
         r = reduce terminate conquer [] c
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

iterDivide(x, p, i) == divide(x)[i]

complete(x) == \A r \in DOMAIN x : x[r] # 0

base(x, p, i) == IF complete(p[i].v) THEN p[i].v ELSE << >>

isBase(x, p, i) == complete(p[i].v) \/ ~ canAddQueens(p[i].v) 
 
conquer(r1, r2) == r1 \o r2

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 1
UpperBnd(x) == Len(divide(x))
Step(i)     == i + 1  

INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

InitCtx(x) == [in  |-> x,
               i_p |-> LowerBnd(x),
               v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               ret |-> << >>,
               ste |-> "OFF"] 

Pre(x) == \A r \in DOMAIN x : x[r] = 0

Eureka(r) == /\ complete(r)
\*             /\ IF complete(r) THEN PrintT("eureka! " \o ToString(r)) ELSE complete(r)  

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall i \in 1..Len(divide(B))
            p[i] = divide B             
   
   PCR:   p = produce divide B                            
*)
P(I) == 
  \E i \in Iterator(I) : 
    /\ ~ Written(v_p(I), i)         
    /\ map' = [map EXCEPT  
         ![I].v_p[i] = [v |-> iterDivide(in(I), v_p(I), i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer non-recursive action
*)
C_base(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ Written(v_c(I), i)
    /\ isBase(in(I), v_p(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> base(in(I), v_p(I), i), r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(base(in(I), v_p(I), i)))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i \in Iterator(I):
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ isBase(in(I), v_p(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r  = 1,
         ![I \o <<i>>]  = InitCtx(v_p(I)[i].v) ]     
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(in(I \o <<i>>)'))                                                                                                                                            

(*
   Consumer recursive return action
*)
C_ret(I) == 
  \E i \in Iterator(I) :
     /\ Read(v_p(I), i)       
     /\ ~ Written(v_c(I), i)
     /\ Finished(I \o <<i>>)   
     /\ map' = [map EXCEPT 
          ![I].v_c[i]= [v |-> Out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(Out(I \o <<i>>)))                

(*
   Consumer action
*)
C(I) == \/ C_base(I)
        \/ C_call(I) 
        \/ C_ret(I) 
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_c(I), i)
    /\ ~ Read(v_c(I), i)
    /\ LET ret == conquer(Out(I), v_c(I)[i].v)
           ste == CDone(I, i) \/ Eureka(ret)
       IN map' = [map EXCEPT 
            ![I].ret      = ret,
            ![I].v_c[i].r = @ + 1,
            ![I].ste      = IF ste THEN "END" ELSE @]
\*    /\ IF State(I)' = "END"
\*       THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I))    
\*                       \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE             

(* 
   PCR NQueensFirst step at index I 
*)
Next(I) == 
  \/ /\ State(I) = "OFF" 
     /\ Start(I)
  \/ /\ State(I) = "RUN" 
     /\ \/ P(I) 
        \/ C(I) 
        \/ R(I)
        \/ Quit(I)
 
=============================================================================
\* Modification History
\* Last modified Sat Sep 26 17:59:47 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
