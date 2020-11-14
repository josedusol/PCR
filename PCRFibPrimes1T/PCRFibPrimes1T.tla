---------------------- MODULE PCRFibPrimes1T -------------------------------

(*
   PCR FibPrimes1
   
   This is an experimental alternative version where we replace the Undef
   and partial function concepts by explicitly defining and mantaining 
   function domains.   
   
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

EXTENDS Typedef, PCRBaseT, TLC

VARIABLE im

----------------------------------------------------------------------------

(* 
   Basic functions                            
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

isPrime(x, p, i) ==
  LET n == p[i].v
      f[d \in Nat] ==
        IF d < 2
        THEN n > 1
        ELSE ~ (n % d = 0) /\ f[d-1]
  IN f[Sqrt(n)]

sum(r1, r2) == r1 + (IF r2 THEN 1 ELSE 0)   

----------------------------------------------------------------------------         

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == x
step(i)     == i + 1  
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpaceT WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step
  
i_p(I)   == im[I]
IndexMap == [cmDom -> IndexType]  

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

initCtx(x) == [in  |-> x,
               v_p |-> << >>,
               v_c |-> << >>,
               ret |-> 0,
               ste |-> "OFF"]

pre(x) == TRUE 

----------------------------------------------------------------------------         
            
(* 
   Producer action
   
   FXML:  for (i=LowerBnd(N); i < UpperBnd(N); Step(i))
            p[i] = fib N            
   
   PCR:   p = produceSeq fib N                              
*)
P(I) == 
  /\ i_p(I) \in iterator(I)
  /\ cm' = [cm EXCEPT 
       ![I].v_p = @ @@ i_p(I) :> [v |-> fib(in(I), v_p(I), i_p(I)), r |-> 0] ]
  /\ im' = [im EXCEPT 
       ![I] = step(i_p(I))]    
  /\ vpDom' = vpDom \union {i_p(I)}     
  /\ UNCHANGED vcDom          
\*  /\ PrintT("P" \o ToString(I \o <<i_p(I)>>) \o " : " \o ToString(v_p(I)[i_p(I)].v'))                  


(* 
   Consumer action
   
   FXML:  forall i \in Dom(p)
            c[i] = isPrime N p[i]

   PCR:   c = consume isPrime N p
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c      = @ @@ i :> [v |-> isPrime(in(I), v_p(I), i), r |-> 0] ]
    /\ vcDom' = vcDom \union {i}        
    /\ UNCHANGED <<im, vpDom>>                                              
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))    
 
(* 
   Reducer action
   
   FXML:  ...
   
   PCR:   r = reduce sum 0 c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ ~ read(v_c(I), i)
    /\ LET newRet == sum(out(I), v_c(I)[i].v)
           endSte == cDone(I, i) \/ eCnd(newRet)
       IN  cm' = [cm EXCEPT 
             ![I].ret      = newRet,
             ![I].v_c[i].r = @ + 1,
             ![I].ste      = IF endSte THEN "END" ELSE @]                                                                            
\*          /\ IF endSte
\*             THEN PrintT("FP1 R" \o ToString(I \o <<i>>) 
\*                                 \o " : in= "  \o ToString(in(I))    
\*                                 \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE   
    /\ UNCHANGED <<im,vpDom,vcDom>>        

(* 
   PCR FibPrimes1 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED im
  \/ /\ state(I) = "RUN"  
     /\ \/ P(I) 
        \/ C(I)
        \/ R(I)
        \/ Quit(I)

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 22:00:28 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed