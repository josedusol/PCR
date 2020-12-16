------------------------ MODULE PCRNQueensFirstDC --------------------------

(*
   PCR NQueensFirstDC
   
   ---------------------------------------------------------------------
     fun divide, isBase, base, conquer, complete, abs, canAddQueenInRow, 
         canAddQueenInCell, canAddQueens, addQueenInRow, addQueen
     
     fun iterDivide(X,p,i) = divide(X)[i]
     
     fun subproblem(X,p,i) = if   isBase(X, p, i)
                             then base(X, p, i)
                             else NQueensFirstDC(X)
   
     fun conquer(r1,r2) = if r1 = [] then r2 else r1
     
     cnd term(r) = not (r = null) and complete(r)
     
     pre NQueensFirstDC = \forall r \in 1..Len(X) : X[r] == 0
   
     PCR NQueensFirstDC(X):
       par
         p = produce iterDivide X
         forall p
           c = consume subproblem X p
         r = reduce term conquer [] c
   ---------------------------------------------------------------------
*)

EXTENDS PCRNQueensFirstDCTypes, PCRBase, TLC

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

\* produce further configurations each with a legally placed new queen
divide(x) == 
  LET N == Len(x)
      F[r \in Nat] ==
        IF r <= N
        THEN IF canAddQueenInRow(x, r)
             THEN <<addQueenInRow(x, r)>> \o F[r+1]
             ELSE F[r+1]
        ELSE <<>> 
  IN F[1]    

iterDivide(x, p, I, i) == divide(x)[i]

complete(x) == \A r \in DOMAIN x : x[r] # 0

base(x, p, I, i) == IF complete(p[i].v) THEN p[i].v ELSE Null

isBase(x, p, I, i) == complete(p[i].v) \/ ~ canAddQueens(p[i].v) 
 
conquer(x, o, c, I, i) == IF o = Null THEN c[i].v ELSE o

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 1
upperBnd(x) == Len(divide(x))
step(i)     == i + 1  
eCnd(r)     == r # Null /\ complete(r)
\*eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpace WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

r0(x) == [v |-> Null, r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
               ste |-> "OFF"] 

pre(x) == \A r \in DOMAIN x : x[r] = 0

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall i \in 1..Len(divide(X))
            p[i] = divide X             
   
   PCR:   p = produce divide X                            
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> iterDivide(in(I), v_p(I), I, i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer non-recursive action
*)
C_base(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> base(in(I), v_p(I), I, i), r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(base(in(I), v_p(I), i)))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ wellDef(I \o <<i>>)
    /\ ~ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I \o <<i>>] = initCtx(v_p(I)[i].v) ]
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(in(I \o <<i>>)'))                                                                                                                                            

(*
   Consumer recursive return action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)     
     /\ ~ written(v_c(I), i)
     /\ wellDef(I \o <<i>>) 
     /\ finished(I \o <<i>>)   
     /\ cm' = [cm EXCEPT 
          ![I].v_c[i] = [v |-> out(I \o <<i>>), r |-> 0]]  
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

   PCR:   c = reduce [] conquer c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == conquer(in(I), out(I), v_c(I), I, i)
           endSte == rDone(I, i) \/ eCnd(newOut)
       IN  cm' = [cm EXCEPT 
             ![I].v_c[i].r = @ + 1,
             ![I].v_r[i]   = [v |-> newOut, r |-> 1],
             ![I].i_r      = i,
             ![I].ste      = IF endSte THEN "END" ELSE @]                                                                            
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE

(* 
   PCR NQueensFirstDC step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)
        \/ C(I) 
        \/ R(I)
        \/ Quit(I)  
 
=============================================================================
\* Modification History
\* Last modified Tue Dec 15 21:00:55 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
