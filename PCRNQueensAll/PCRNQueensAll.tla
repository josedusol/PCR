-------------------------- MODULE PCRNQueensAll ----------------------------

(*
   PCR NQueensAll 
   
   ---------------------------------------------------------------------
     fun divide, isBase, base, conquer, complete, canAddQueen, 
         addQueen, abs
     
     fun iter_divide(B, j) = divide(B)[j]
     
     fun divide(B, j) = B WITH j   <- j
                               sol <- addQueen(B.sol, B.i, j)
     
     fun lbnd iter_divide = lambda x. 1 
     fun ubnd iter_divide = lambda x. Len(x.sol) 
     fun step iter_divide = lambda x. x + 1
     
     fun subproblem(B, p, j) = if   isBase(B, p, j)
                               then base(B, p, j)
                               else NQueensAll(B WITH i <- i+1, p, j)
   
     fun conquer(a, b) = a union b
   
     PCR NQueensAll(B):
       par
         p = produce iter_divide B
         forall p
           c = consume subproblem B p
         r = reduce conquer [] c
   ---------------------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

InitCtx(input) == [in  |-> input,
                   i_p |-> LowerBnd(input),
                   v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   ret |-> {},
                   ste |-> OFF] 

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

abs(r) == IF r < 0 THEN -r ELSE r

canAddQueen(sol, i, j) == 
   /\ \A r \in DOMAIN sol : sol[r] # i               \* not in same row
   /\ sol[j] = 0                                     \* not in same column
   /\ \A r \in DOMAIN sol :                          \* not in same diagonal
         sol[r] # 0 => abs(sol[r] - i) # abs(r - j)
                        
addQueen(sol, i, j) == [sol EXCEPT ![j] = i]                         

divide(x, p, j) == [x EXCEPT !.j   = j,
                             !.sol = addQueen(@, x.i, j)]

iterDivide(x, p, j) == divide(x, p, j)[j]

complete(x) == \A r \in DOMAIN x.sol : x.sol[r] # 0

base(x, p, j) == IF complete(x) THEN { x.sol } ELSE {}

isBase(x, p, j) == complete(x) \/ ~ canAddQueen(x.sol, x.i, j) 
 
conquer(old, new) == old \union new

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall j \in 1..Len(B.sol)
            p[j] = divide B             
   
   PCR:   p = produce divide B                            
*)
P(i) == 
  \E j \in Len() : 
    /\ ~ Written(v_p(i), j)         
    /\ map' = [map EXCEPT  
         ![i].v_p[j] = [v |-> iterDivide(in(i), v_p(i), j), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(j) \o " : " \o ToString(v_p(i)[j].v'))                  

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
\*    /\ PrintT("C_base " \o ToString(j) \o " : P" \o ToString(j) 
\*                        \o " con v=" \o ToString(v_p(i)[j].v))

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
         ![i \o <<j>>]  = InitCtx([v_p(i)[j].v EXCEPT !.i = @ + 1]) ]     
\*    /\ PrintT("C_call " \o ToString(i \o <<j>>) 
\*                        \o " : in= " \o ToString(in(i \o <<j>>)'))                                                                                                                                            

(*
   Consumer recursive end action
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
    /\ map' = [map EXCEPT 
         ![i].ret      = conquer(@, v_c(i)[j].v),
         ![i].v_c[j].r = @ + 1,
         ![i].ste      = IF CDone(i, j) THEN END ELSE @]                                                                            
\*    /\ IF   CDone(i, j)
\*       THEN PrintT("NQ: in= "  \o ToString(in(i))
\*                   \o " ret= " \o ToString(Out(i)'))
\*       ELSE TRUE             

Next(i) == 
  \/ /\ State(i) = OFF 
     /\ Start(i)
  \/ /\ State(i) = RUN 
     /\ \/ P(i) 
        \/ C(i) 
        \/ R(i)
        \/ Quit(i)
 
=============================================================================
\* Modification History
\* Last modified Fri Sep 18 22:45:49 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
