------------------------ MODULE PCRKnapSack01Step --------------------------

(*
   PCR KnapSack01Step
   
   ---------------------------------------------------------------------
     fun init, getLast, nextItem, solve, update 
          
     fun until(y, i) = i > Len(y[0].data.w)
        
     PCR KnapSack01(X):
       par
         p = produce init X
         forall p
           c = iterate until KnapSack01Step p
         r = reduce getLast 0 c
         
     PCR KnapSack01Step(Sol, k):
       par
         p = produce id Sol k
         forall p
           c = consume solve Sol k p
         r = reduce update Sol c   
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01Types, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

max(x, y) == IF x >= y THEN x ELSE y

id(x1, x2, p, i) == i
 
solve(x1, x2, p, i) ==   \* i is capacity column j:  0 <= j <= C
  LET data == x1.data      
      row  == x1.row
      it   == x2
      j    == i + 1
  IN  [i    |-> j,
       v    |-> CASE  it = 0           ->  0         \* never happen
                  []  data.w[it] >  i  ->  row[j] 
                  []  data.w[it] <= i  ->  max(row[j],  row[j-data.w[it]] + data.v[it]) ]
                       
update(r, z) == [z EXCEPT !.row[z.i] = z.v]   

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
   PCR KnapSack01Step step at index I 
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
\* Last modified Mon Nov 09 21:45:53 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
