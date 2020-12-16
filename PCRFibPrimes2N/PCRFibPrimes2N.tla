-------------------------- MODULE PCRFibPrimes2N ---------------------------

(*
   PCR FibPrimes2N
   
   ----------------------------------------------------------
     fun fib, sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun fib(N,p,i) = if i < 2 then 1 else p[i-1] + p[i-2]
     fun sum(r1,r2) = r1 + (if r2 then 1 else 0)  

     dep p(i-1) -> p(i)
     dep p(i-2) -> p(i)
   
     PCR FibPrimes2(N):
       par
         p = produce fib N
         forall p
           c = consume isPrime p   \\ call isPrime PCR as a function
         r = reduce sum 0 c
   ----------------------------------------------------------
*)

EXTENDS PCRFibPrimes2NTypes, PCRBaseN, TLC

VARIABLES cm2

----------------------------------------------------------------------------

(* 
   Basic functions                          
*)

fib(x, p, I, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

sum(x, o, c, I, i) == o + (IF c[i].v THEN 1 ELSE 0)  

isPrime == INSTANCE PCRIsPrimeN WITH
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- <<VarC1Type2>>,
  VarRType  <- VarRType2,
  cm        <- cm2

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == x
step(i)     == i + 1  
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpaceN WITH
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
               v_c |-> <<[i \in IndexType |-> Undef]>>,
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
   Consumer call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ isPrime!wellDef(I \o <<i>>)
    /\ cm'  = [cm  EXCEPT 
         ![I].v_p[i].r = @ + 1] 
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = isPrime!initCtx(v_p(I)[i].v) ]   
\*    /\ PrintT("C_call" \o ToString(I \o <<j>>) 
\*                       \o " : in= " \o ToString(v_p(I)[j].v))                                                                                                                                            

(*
   Consumer end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)    
    /\ ~ written(v_c(1,I), i)
    /\ isPrime!wellDef(I \o <<i>>) 
    /\ isPrime!finished(I \o <<i>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c[1][i] = [v |-> isPrime!out(I \o <<i>>), r |-> 0]]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(isPrime!in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(isPrime!Out(I \o <<i>>)))

(*
   Consumer action
*)
C(I) == \/ C_call(I)
        \/ C_ret(I)  /\ UNCHANGED cm2   

(* 
   Reducer action

   PCR:  c = reduce sum 0 c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(1,I), i)
    /\ pending(I, i)
    /\ LET newOut == sum(in(I), out(I), v_c(1,I), I, i)
           endSte == rDone(I, i) \/ eCnd(newOut)
       IN  cm' = [cm EXCEPT 
             ![I].v_c[1][i].r = @ + 1,
             ![I].v_r[i]      = [v |-> newOut, r |-> 1],
             ![I].i_r         = i,
             ![I].ste         = IF endSte THEN "END" ELSE @]                                                                            
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE  

(* 
   PCR FibPrimes2N step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED cm2
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)      /\ UNCHANGED cm2
        \/ C(I)
        \/ R(I)      /\ UNCHANGED cm2
        \/ Quit(I)   /\ UNCHANGED cm2         

=============================================================================
\* Modification History
\* Last modified Wed Dec 16 15:09:29 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
