---------------------- MODULE PCRFibPrimes1 --------------------------------

(*
   PCR FibPrimes1
   
   ----------------------------------------------------------
     fun fib, isPrime, sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun fib(N,p,i) = if i < 2 then 1 else p[i-1] + p[i-2]
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

VARIABLE i_p

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                            
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

isPrime(x, p, i) ==
  LET n == p[i].v
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
Step(i)     == i + 1  
ECnd(r)     == FALSE
 
INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step,
  ECnd      <- ECnd,
  i_p       <- i_p

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

InitCtx(x) == [in  |-> x,
\*               i_p |-> LowerBnd(x),
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
       ![I].v_p[i_p] = [v |-> fib(in(I), v_p(I), i_p), r |-> 0] ]
\*       ![I].i_p      = Step(@)]
  /\ i_p' = Step(i_p)              
\*  /\ PrintT("P" \o ToString(I \o <<i_p(I)>>) \o " : " \o ToString(v_p(I)[i_p(I)].v'))                  

(* 
   Consumer action
   
   FXML:  forall i \in Dom(p)
            c[i] = isPrime N p[i]

   PCR:   c = consume isPrime N p
*)
C(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ Written(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r = 1, 
         ![I].v_c[i]   = [v |-> isPrime(in(I), v_p(I), i), r |-> 0]]                          
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))    
 
(* 
   Reducer action
   
   FXML:  ...
   
   PCR:   r = reduce sum 0 c
*)
R(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_c(I), i)
    /\ ~ Read(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].ret      = sum(@, v_c(I)[i].v),
         ![I].v_c[i].r = @ + 1,
         ![I].ste      = IF CDone(I, i) THEN "END" ELSE @]                                                                            
\*    /\ IF   CDone(I, i)
\*       THEN PrintT("FP1 R" \o ToString(I \o <<i>>) 
\*                           \o " : in= "  \o ToString(in(I))    
\*                           \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE           

(* 
   PCR FibPrimes1 step at index I 
*)
Next(I) == 
  \/ /\ State(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED i_p
  \/ /\ State(I) = "RUN"  
     /\ \/ P(I) 
        \/ C(I)      /\ UNCHANGED i_p
        \/ R(I)      /\ UNCHANGED i_p
        \/ Eureka(I) /\ UNCHANGED i_p
        \/ Quit(I)   /\ UNCHANGED i_p

=============================================================================
\* Modification History
\* Last modified Tue Sep 29 15:16:10 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
