----------------------- MODULE PCRKnapSack01_4Step -------------------------

(*
   PCR KnapSack01_4Step
   
   ---------------------------------------------------------------------
     fun init, until, getLast, nextItem, solve, update  
        
     fun until(X, i, y, y_i) = y_i > X.n
        
     PCR KnapSack01_4(X):
       par
         p = produce init X
         forall p
           par
             c1 = iterate until KnapSack01_4Step X p
             c2 = consume backtrack X c1
         r = reduce retSol [] c1 c2
         
     PCR KnapSack01Step_4(X, S, k):
       par
         p = produce id X S k
         forall p
           c = consume solve X S k p
         r = reduce update S X S c 
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01_4Types, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

max(x, y) == IF x >= y THEN x ELSE y

id(x, p, I, j) == j
 
solve(x, p, I, j) ==              \* capacity j where 0 <= j <= C
  LET v     == x[1].v             \* item values 
      w     == x[1].w             \* item weights 
      table == x[2]               \* profit table
      i     == x[3]               \* current item 
  IN  [c |-> <<i, j>>,
       v |-> CASE i = 0      ->  0                   \* never happen
               [] w[i] >  j  ->  table[<<i-1, j>>]
               [] w[i] <= j  ->  max(table[<<i-1, j>>], 
                                     table[<<i-1, j - w[i]>>] + v[i]) ]
                       
update(x, o, c, I, i) == [o EXCEPT ![c[i].v.c] = c[i].v.v] 

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

r0(x) == [v |-> x[2], 
          r |-> 0]

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
   
   FXML:  forall i \in 1..Len(B)
            c[i] = init B[i]             
   
   PCR:   c = produce elem B                            
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> id(in(I), v_p(I), I, i), r |-> 0] ]             
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
         ![I].v_c[i]   = [v |-> solve(in(I), v_p(I), I, i), r |-> 0]]                                          
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  

(* 
   Reducer action
   
   FXML:  ...

   PCR:   c = reduce update S X S c 
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
\* Last modified Tue Dec 15 20:58:56 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
