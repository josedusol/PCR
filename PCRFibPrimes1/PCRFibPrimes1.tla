---------------------- MODULE PCRFibPrimes1 --------------------------------

(*
   PCR FibPrimes1
   
   ----------------------------------------------------------
     fun fib, isPrime, sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun fib(N, p, j) = if j < 2 then 1 else p[j-1] + p[j-2]
     fun sum(r1,r2) = r1 + (if r2 then 1 else 0)
   
     PCR FibPrimes1(N):
       par
         p = produceSeq fib N
         forall p
           c = consume isPrime N p
         r = reduce sum 0 c
   ----------------------------------------------------------  
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                            
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

isPrime(x, p, j) ==
  LET n == p[j].v
      F[d \in Nat] ==
        IF d < 2
        THEN n > 1
        ELSE ~ (n % d = 0) /\ F[d-1]
  IN F[Sqrt(n)]

sum(r1, r2) == r1 + (IF r2 THEN 1 ELSE 0)   

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
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = isPrime N p[j]

   PCR:   c = consume isPrime N p
*)
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = 1, 
         ![i].v_c[j]   = [v |-> isPrime(in(i), v_p(i), j), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(i \o <<j>>) \o " : P" \o ToString(j) 
\*                  \o " con v=" \o ToString(v_p(i)[j].v))    
 
(* 
   Reducer action
   
   FXML:  ...
   
   PCR:   r = reduce sum 0 c
*)
R(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_c(i), j)
    /\ ~ Read(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].ret      = sum(@, v_c(i)[j].v),
         ![i].v_c[j].r = @ + 1,
         ![i].ste      = IF CDone(i, j) THEN "END" ELSE @]                                                                            
\*    /\ IF   CDone(i, j)
\*       THEN PrintT("FP1 R" \o ToString(i \o <<j>>) 
\*                           \o " : in= "  \o ToString(in(i))    
\*                           \o " : ret= " \o ToString(Out(i)')) 
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
\* Last modified Wed Sep 23 23:51:35 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
