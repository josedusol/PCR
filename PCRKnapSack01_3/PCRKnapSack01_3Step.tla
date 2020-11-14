----------------------- MODULE PCRKnapSack01_3Step -------------------------

(*
   PCR KnapSack01_3Step
   
   This is a variant of PCRKnapSack01 where we try to implement the Iterate
   PCR construct using an auxiliary PCR with sequential producer and also
   imposing some extra dependencies between consumer and reducer.  
   
   ---------------------------------------------------------------------
     fun init, getLast, apply, pass, retLast, solve, update  
     
     lbnd init = lambda x. 0 
     ubnd init = lambda x. 0                 \\ just one instance
        
     PCR KnapSack01_3(X):
       par
         p = produce init X
         forall p
           c = consume KnapSack01_3Iterate p
         r = reduce getLast [] c
         
     fun apply(Y, p, i) = if i = 0 
                          then Y                            \\ initial value
                          else KnapSack01_3Step(p[i-1], i)  \\ apply step on previous value      
     fun pass(Y, p, i) = p[i]     
     fun retLast(r, c, i) = c.last
         
     lbnd apply = lambda x. 0 
     ubnd apply = lambda x. Len(x.data.w)    \\ iterate sequentially on number of items to consider
     step apply = lambda i. i + 1   
     
     dep c(i-1) -> c(i)                     \\ consumers should also be sequential
     dep c(i..) -> r(i)                     \\ reducer should wait for consumer future
         
     PCR KnapSack01_3Iterate(Y):            \\ auxiliary PCR to simulate "iterate" construct
       par
         p = produceSeq apply Y
         forall p
           c = consume pass Y p
         r = reduce retLast Y c             \\ we just want the last value of c

     lbnd id = lambda x. 0 
     ubnd id = lambda x. Len(x[0].C)        \\ solve in paralell for all weights <= C
     step id = lambda i. i + 1
         
     PCR KnapSack01_3Step(Y, k):
       par
         p = produce id Y k
         forall p
           c = consume solve Y k p
         r = reduce update Y c     
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01_3Types, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

max(x, y) == IF x >= y THEN x ELSE y

id(x1, x2, p, i) == i

solve(x1, x2, p, j) ==   \* capacity j where 0 <= j <= C
  LET v   == x1.data.v   \* item values 
      w   == x1.data.w   \* item weights 
      row == x1.row      \* profit row for i-1
      i   == x2          \* current item 
  IN  [j |-> j,
       v |-> CASE i = 0      ->  0             \* never happen
               [] w[i] >  j  ->  row[j+1] 
               [] w[i] <= j  ->  max(row[j+1],  
                                     row[(j+1)-w[i]] + v[i]) ]
                       
update(r, z) == [r EXCEPT !.row[z.j+1] = z.v]   

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == x[1].data.C
step(i)     == i + 1  
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpace WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               ret |-> x[1],
               ste |-> "OFF"] 

pre(x) == TRUE

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall i \in 1..Len(B)
            c[i] = init B[i]             
   
   PCR:   c = produce elem B                            
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> id(in1(I), in2(I), v_p(I), i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(* 
   Consumer action
   
   FXML:  forall i \in Dom(p)
            cs[i] = extend X c[i]

   PCR:   cs = consume extend B c
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> solve(in1(I), in2(I), v_p(I), i), r |-> 0]]                                          
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ ~ read(v_c(I), i)
    /\ LET newRet == update(out(I), v_c(I)[i].v)
           endSte == cDone(I, i) \/ eCnd(newRet)
       IN  cm' = [cm EXCEPT 
             ![I].ret      = newRet,
             ![I].v_c[i].r = @ + 1,
             ![I].ste      = IF endSte THEN "END" ELSE @]
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE             

(* 
   PCR KnapSack01_3Step step at index I 
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
\* Last modified Fri Nov 13 22:10:56 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
