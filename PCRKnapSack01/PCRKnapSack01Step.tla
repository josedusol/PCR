------------------------ MODULE PCRKnapSack01Step --------------------------

(*
   PCR KnapSack01Step
   
   ---------------------------------------------------------------------
     fun init, getLast, nextItem, solve, update 
          
     cnd found(r) = not (r == null) and complete(r)
        
     PCR KnapSack01(X):
       par
         p = produce id X
         forall p
           c = iterate found KnapSack01Step p
         r = reduce getLast [] c
         
     PCR KnapSack01Step(Sol):
       par
         p = produce nextItem Sol
         forall p
           c = consume solve Sol p
         r = reduce update Sol c   
   ---------------------------------------------------------------------
*)

EXTENDS Typedef, FiniteSets, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

max(x, y) == IF x >= y THEN x ELSE y

nextItem(x, p, i) == x.item + 1
 
solve(x, p, i) ==   \* i is capacity column j:  0 <= j <= C
  LET data == x.data
      it   == p[i].v
      row  == x.row
      j    == i + 1
  IN  [item |-> it,
       i    |-> j,
       v    |-> CASE  it = 0           ->  0         \* never happen
                  []  data.w[it] >  i  ->  row[j] 
                  []  data.w[it] <= i  ->  max(row[j],  row[j-data.w[it]] + data.v[it]) ]
                       
update(r1, r2) == [r1 EXCEPT !.item      = r2.item,
                             !.row[r2.i] = r2.v ]   

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == x.data.C
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
               v_p |-> [n \in IndexType |-> Undef],
               v_c |-> [n \in IndexType |-> Undef],
               ret |-> x,
               ste |-> "OFF"] 

pre(x) == TRUE

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall i \in 1..Len(B)
            c[i] = elem B[i]             
   
   PCR:   c = produce elem B                            
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> nextItem(in(I), v_p(I), i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(* 
   Consumer action
   
   FXML:  forall i \in Dom(p)
            cs[i] = extend B c[i]

   PCR:   cs = consume extend B c
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
\*    /\ ~ read(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> solve(in(I), v_p(I), i), r |-> 0]]                                          
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
   PCR NQueensFirstIt step at index I 
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
\* Last modified Wed Nov 04 22:55:23 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
