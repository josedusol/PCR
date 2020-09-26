------------------------- MODULE PCRIsPrimeNaive ---------------------------

(*
   PCR IsPrimeNaive
   
   ----------------------------------------------------------
     fun divisors, notDivides, and
     
     fun divisors(N,p,j) = j
     fun notDivides(N,p,j) = if 2 <= p[j] && p[j] < N
                             then not (N % p[j] == 0)
                             else True
     fun and(a,b) = a && b 
     
     lbnd divisors = lambda x. 0 
     ubnd divisors = lambda x. x
     step divisors = lambda x. x+1
   
     PCR IsPrimeNaive(N):
       par
         p = produce divisors N
         forall p
           c = consume notDivides N 
         r = reduce and (N > 1) c
   ----------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

divisors(x, p, j) == j
   
notDivides(x, p, j) == IF 2 <= p[j].v /\ p[j].v < x
                       THEN ~ (x % p[j].v = 0)
                       ELSE TRUE

and(old, new) == old /\ new 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 0
UpperBnd(x) == x
Step(j)     == j + 1          
 
INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step
                      
InitCtx(x) == [in  |-> x,
               i_p |-> LowerBnd(x),
               v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               ret |-> x > 1,
               ste |-> "OFF"]  

Pre(x) == TRUE

----------------------------------------------------------------------------
                                          
(* 
   Producer action
   
   FXML:  forall j \in 0..N
            p[j] = divisors N               
   
   PCR:   p = produce divisors N
*)
P(i) == 
  \E j \in Iterator(i) :
    /\ ~ Written(v_p(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j] = [v |-> divisors(in(i), v_p(i), j), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(i \o <<j>>) \o " : " \o ToString(v_p(i)[j].v'))  

(* 
   Consumer action
   
   FXML:  forall j \in Dom(p) 
            c[j] = notDivides N p[j] 

   PCR:   c = consume notDivides N
*) 
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = @ + 1,
         ![i].v_c[j]   = [v |-> notDivides(in(i), v_p(i), j), r |-> 0] ]               
\*    /\ PrintT("C" \o ToString(i \o <<j>>) \o " : P" \o ToString(j) 
\*                  \o " con v=" \o ToString(v_p(i)[j].v))       

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce and (N > 1) c
*)
R(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_c(i), j)    
    /\ ~ Read(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].ret      = and(@, v_c(i)[j].v),
         ![i].v_c[j].r = @ + 1,
         ![i].ste      = IF CDone(i, j) THEN "END" ELSE @]
\*    /\ IF   CDone(i, j)
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
\* Last modified Wed Sep 23 19:04:19 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
