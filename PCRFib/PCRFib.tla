----------------------------- MODULE PCRFib --------------------------------

(*
   PCR Fib
   
   ----------------------------------------------------------
     fun fib, checkLast, projectRed
     
     lbnd projectProd = lambda x. 0 
     ubnd projectProd = lambda x. x
     
     fun fib(N,p,j) = if j < 2 then 1 else p[j-1] + p[j-2]
     fun checkLast(N,p,j) = if j < N then 0 else p[j]
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

checkLast(x, p, j) == IF j < x THEN 0 ELSE p[j].v 

projectRed(r1, r2) == r1 + r2 

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
               ret |-> 0,
               ste |-> "OFF"]  

Pre(x) == TRUE

----------------------------------------------------------------------------

(* 
   Producer action
   
   FXML:  for (j=LowerBnd(N); j < UpperBnd(N); Step(j))
            p[j] = fib N            
   
   PCR:   p = produceSeq fib N                              
*)
P(i) == 
  /\ Bound(i) 
  /\ map' = [map EXCEPT 
       ![i].v_p[i_p(i)] = [v |-> fib(in(i), v_p(i), i_p(i)), r |-> 0],
       ![i].i_p         = Step(@)]         
\*  /\ PrintT("P" \o ToString(i \o <<i_p(i)>>) \o " : " \o ToString(v_p(i)[i_p(i)].v')) 
                                          

(*
   Consumer non-recursive action
*)
C_base(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ v_p(i)[j].v < 2
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = @ + 1,
         ![i].v_c[j]   = [v |-> 1, r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(j) \o " : P" \o ToString(j) 
\*                       \o " con v=" \o ToString(v_p(i)[j].v))

(* 
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = checkLast N p[j]

   PCR:   c = consume checkLast N p
*)
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = 1, 
         ![i].v_c[j]   = [v |-> checkLast(in(i), v_p(i), j), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(i \o <<j>>) \o " : P" \o ToString(j) 
\*                  \o " con v=" \o ToString(v_p(i)[j].v))  

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce projectRed 0 c
*)
R(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_c(i), j)    
    /\ ~ Read(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].ret      = projectRed(@, v_c(i)[j].v),
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
\* Last modified Fri Sep 25 13:46:36 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
