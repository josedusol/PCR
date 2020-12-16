---------------------- MODULE PCRFibPrimes1 --------------------------------

(*
   PCR FibPrimes1
   
   This is an experimental alternative version where Undef is handled
   as a constant of the Spec.
   
   ----------------------------------------------------------
     fun fib, isPrime, sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun fib(N,p,i) = if i < 2 then 1 else p[i-1] + p[i-2]
     fun sum(r,z) = r + (if z then 1 else 0)
   
     dep p(i-1) -> p(i)
     dep p(i-2) -> p(i)   
   
     PCR FibPrimes1(N):
       par
         p = produce fib N
         forall p
           c = consume isPrime N p
         r = reduce sum 0 c
   ----------------------------------------------------------  
*)

EXTENDS PCRFibPrimes1Types, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                            
*)

fib(x, p, I, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

isPrime(x, p, I, i) ==
  LET n == p[i].v
      f[d \in Nat] ==
        IF d < 2
        THEN n > 1
        ELSE ~ (n % d = 0) /\ f[d-1]
  IN f[Sqrt(n)]

sum(x, o, c, I, i) == o + (IF c[i].v THEN 1 ELSE 0)   

----------------------------------------------------------------------------         

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == x
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

r0(x) == [v |-> 0, r |-> 0]

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
   
   PCR:  p = produce fib N                          
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ i > lowerBnd(in(I))     => written(v_p(I), i-1)
    /\ i > lowerBnd(in(I)) + 1 => written(v_p(I), i-2)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> fib(in(I), v_p(I), I, i), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))

(* 
   Consumer action

   PCR:  c = consume isPrime N p
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> isPrime(in(I), v_p(I), I, i), r |-> 0] ]                                            
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))    

(* 
   Reducer action
   
   PCR:  c = reduce sum 0 c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == sum(in(I), out(I), v_c(I), I, i)
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
   PCR FibPrimes1 step at index I 
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
\* Last modified Wed Dec 16 15:08:35 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
