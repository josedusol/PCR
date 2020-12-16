----------------------- MODULE PCRKnapSack01_1Step -------------------------

(*
   PCR KnapSack01_1Step
   
   ---------------------------------------------------------------------
     fun init, until, getLast, id, solve, update 
          
     fun until(X, i, y, y_i) = y_i > X.n
        
     PCR KnapSack01_1(X):
       par
         p = produce init X
         forall p
           c = iterate until KnapSack01_1Step X p
         r = reduce getLast 0 X c
         
     PCR KnapSack01_1Step(X, row, k):
       par
         p = produce id X row k
         forall p
           c = consume solve X row k p
         r = reduce update row X row k c
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01_1Types, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

max(x, y) == IF x >= y THEN x ELSE y

id(x, p, I, j) == j

solve(x, p, I, j) ==                \* capacity j where 0 <= j <= C
  LET v   == x[1].v                 \* item values 
      w   == x[1].w                 \* item weights 
      row == x[2]                   \* profit row for i-1
      i   == x[3]                   \* current item
  IN  CASE  i = 0      ->  0                              \* never happen
        []  w[i] >  j  ->  row[j+1] 
        []  w[i] <= j  ->  max(row[j+1],  
                               row[(j+1)-w[i]] + v[i])
                       
update(x, o, c, I, j) == [o EXCEPT ![j+1] = c[j].v] 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == x[1].C
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

r0(x) == [v |-> x[2], r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
               ste |-> "OFF"] 

pre(x) == TRUE

----------------------------------------------------------------------------
            
(* 
   Producer action

   PCR:  p = produce id X row k                          
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> id(in(I), v_p(I), I, i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(* 
   Consumer action
   
   PCR:  c = consume solve X row k p
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> solve(in(I), v_p(I), I, i), r |-> 0]]                                          
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))           

(* 
   Reducer action

   PCR:  r = reduce update row X row k c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == update(in(I), out(I), v_c(I), I, i)
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
\* Last modified Wed Dec 16 16:04:51 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
