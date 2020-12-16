-------------------------- MODULE PCRFibPrimes4 ----------------------------

(*
   PCR FibPrimes4
   
   ----------------------------------------------------------
     fun isPrime, sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun sum(r1,r2) = r1 + (if r2 then 1 else 0)  
   
     dep p(i-1) -> p(i)
     dep p(i-2) -> p(i)
   
     PCR FibPrimes4(N):
       par
         p = produce fibRec p     \\ call fibRec PCR as a function
         forall p
           c = consume isPrime N p
         r = reduce sum 0 c
   ----------------------------------------------------------
*)

EXTENDS PCRFibPrimes4Types, PCRBase, TLC

VARIABLES cm2

----------------------------------------------------------------------------

(* 
   Basic functions                          
*)

isPrime(x, p, I, i) ==
  LET n == p[i].v
      F[d \in Nat] ==
        IF d < 2
        THEN n > 1
        ELSE ~ (n % d = 0) /\ F[d-1]
  IN F[Sqrt(n)]

sum(x, o, c, I, i) == o + (IF c[i].v THEN 1 ELSE 0)  

fibRec == INSTANCE PCRFibRec WITH
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
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
   Producer call action
*)
P_call(I) == 
  \E i \in iterator(I) :
    /\ i > lowerBnd(in(I))     => written(v_p(I), i-1)
    /\ i > lowerBnd(in(I)) + 1 => written(v_p(I), i-2)  
    /\ ~ fibRec!wellDef(I \o <<i>>)
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = fibRec!initCtx(i) ]                  
\*    /\ PrintT("P_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(i))

(*
   Producer ret action
*)
P_ret(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ fibRec!wellDef(I \o <<i>>)
    /\ fibRec!finished(I \o <<i>>)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> fibRec!out(I \o <<i>>), r |-> 0]] 
\*  /\ PrintT("P_ret" \o ToString(I \o <<i>>) 
\*                    \o " : in= "  \o ToString(fibRec!in(I \o <<i>>))    
\*                    \o " : ret= " \o ToString(fibRec!out(I \o <<i>>)))

(*
   Producer action
*)
P(I) == \/ P_call(I) /\ UNCHANGED cm
        \/ P_ret(I)  /\ UNCHANGED cm2  

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
         ![I].v_c[i]   = [v |-> isPrime(in(I), v_p(I), I, i), r |-> 0]]                         
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
   PCR FibPrimes4 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED cm2
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)
        \/ C(I)      /\ UNCHANGED cm2
        \/ R(I)      /\ UNCHANGED cm2
        \/ Quit(I)   /\ UNCHANGED cm2           

=============================================================================
\* Modification History
\* Last modified Wed Dec 16 15:09:58 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
