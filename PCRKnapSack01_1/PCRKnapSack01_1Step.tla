----------------------- MODULE PCRKnapSack01_1Step -------------------------

(*
   PCR KnapSack01_1Step
   
   ---------------------------------------------------------------------
     fun init, until, getLast, id, solve, update 
          
     fun until(y, i) = i > i > y[0].data.n
        
     PCR KnapSack01_1(X):
       par
         p = produce init X
         forall p
           c = iterate until KnapSack01_1Step p
         r = reduce getLast 0 c
         
     PCR KnapSack01_1Step(Sol, k):
       par
         p = produce id Sol k
         forall p
           c = consume solve Sol k p
         r = reduce update Sol c   
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01_1Types, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

max(x, y) == IF x >= y THEN x ELSE y

id(x1, x2, p, j) == j
 
solve(x1, x2, p, j) ==   \* capacity j where 0 <= j <= C
  LET v   == x1.data.v   \* item values 
      w   == x1.data.w   \* item weights 
      row == x1.row      \* profit row for i-1
      i   == x2          \* current item
  IN  [j |-> j,
       v |-> CASE  i = 0      ->  0            \* never happen
               []  w[i] >  j  ->  row[j+1] 
               []  w[i] <= j  ->  max(row[j+1],  
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
   PCR KnapSack01_1Step step at index I 
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
\* Last modified Fri Nov 13 22:26:34 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
