---------------------- MODULE PCRFibPrimes1 --------------------------------

(*
   PCR FibPrimes1
   
   ----------------------------------------------------------
     fun fib, isPrime, sum
   
     fun lbnd fib = lambda x. 0 
     fun ubnd fib = lambda x. x
     fun step fib = lambda x. x + 1
   
     PCR FibPrimes1(N):
       par
         p = produceSeq fib N
         forall p
           c = consume isPrime p
         r = reduce sum 0 c
   ----------------------------------------------------------  
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

InitCtx(input) == [in  |-> input,
                   i_p |-> LowerBnd(input),
                   v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   ret |-> 0,
                   ste |-> OFF]

----------------------------------------------------------------------------

(* 
   Basic functions                            
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

isPrime(x, p, j) == LET div(k,m) == \E d \in 1..m : m = k * d
                        val      == p[j].v
                    IN val > 1 /\ ~ \E m \in 2..val-1 : div(m, val)           

sum(old, new) == old + (IF new THEN 1 ELSE 0)   

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
\*  /\ PrintT("P" \o ToString(j) \o " : " \o ToString(v_p(i)[j].v'))                  

(* 
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = isPrime p[j]

   PCR:   c = consume isPrime p
*)
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = 1, 
         ![i].v_c[j]   = [v |-> isPrime(in(i), v_p(i), j), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(j) \o " : P" \o ToString(j) 
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
         ![i].ste      = IF CDone(i, j) THEN END ELSE @]                                                                            
\*    /\ IF CDone(i, j)
\*       THEN PrintT("FP: in= " \o ToString(in(i)) 
\*                              \o " ret= " \o ToString(out(i)'))
\*       ELSE TRUE              

Next(i) == 
  \/ /\ State(i) = OFF 
     /\ Start(i)
  \/ /\ State(i) = RUN  
     /\ \/ P(i) 
        \/ C(i) 
        \/ R(i)
        \/ Quit(i)

=============================================================================
\* Modification History
\* Last modified Sat Sep 12 18:07:33 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
