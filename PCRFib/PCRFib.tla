----------------------------- MODULE PCRFib --------------------------------

(*
   PCR Fib
   
   ----------------------------------------------------------
     fun fib, checkLast, projectRed
     
     lbnd projectProd = lambda x. 0 
     ubnd projectProd = lambda x. x
     
     fun fib(N,p,i) = if i < 2 then 1 else p[i-1] + p[i-2]
     fun checkLast(N,p,i) = if i < N then 0 else p[i]
     fun projectRed(r1,r2) = r2 
 
     PCR Fib(N):
       par
         p = produceSeq fib N
         forall p
           c = consume id N p
         r = reduce projectRed 0 c
   ----------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

checkLast(x, p, i) == IF i < x THEN 0 ELSE p[i].v 

projectRed(r1, r2) == r1 + r2 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 0
UpperBnd(x) == x
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
               ret |-> 0,
               ste |-> "OFF"]  

Pre(x) == TRUE

----------------------------------------------------------------------------

(* 
   Producer action
   
   FXML:  for (i=LowerBnd(N); i < UpperBnd(N); Step(i))
            p[i] = fib N            
   
   PCR:   p = produceSeq fib N                              
*)
P(I) == 
  /\ Bound(I) 
  /\ map' = [map EXCEPT 
       ![I].v_p[i_p(I)] = [v |-> fib(in(I), v_p(I), i_p(I)), r |-> 0],
       ![I].i_p         = Step(@)]         
\*  /\ PrintT("P" \o ToString(I \o <<i_p(I)>>) \o " : " \o ToString(v_p(I)[i_p(I)].v')) 
                                          
(* 
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = checkLast N p[j]

   PCR:   c = consume checkLast N p
*)
C(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ Written(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r = 1, 
         ![I].v_c[i]   = [v |-> checkLast(in(I), v_p(I), i), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce projectRed 0 c
*)
R(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_c(I), i)    
    /\ ~ Read(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].ret      = projectRed(@, v_c(I)[i].v),
         ![I].v_c[i].r = @ + 1,
         ![I].ste      = IF CDone(I, i) THEN "END" ELSE @]
\*    /\ IF   CDone(I, i)
\*       THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I))    
\*                       \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE    

(* 
   PCR Fib step at index I 
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
\* Last modified Sat Sep 26 16:03:15 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
