-------------------------- MODULE PCRFibPrimes6 ----------------------------

(*
   PCR FibPrimes6
   
   ----------------------------------------------------------
     fun sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun sum(r1,r2) = r1 + (if r2 then 1 else 0)  
   
     dep p(i-1) -> p(i)
     dep p(i-2) -> p(i)
   
     PCR FibPrimes6(N):
       par
         p = produce fib p        \\ call fib PCR as a function
         forall p
           c = consume isPrime p  \\ call isPrime PCR as a function
         r = reduce sum 0 c
   ----------------------------------------------------------
*)

EXTENDS PCRFibPrimes6Types, PCRBase, TLC

VARIABLES cm2, cm3

----------------------------------------------------------------------------

(* 
   Basic functions                          
*)

sum(x, o, c, I, i) == o + (IF c[i].v THEN 1 ELSE 0)  

fib == INSTANCE PCRFib WITH
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  cm        <- cm2

isPrime == INSTANCE PCRIsPrime WITH
  InType    <- InType3,
  CtxIdType <- CtxIdType3,
  IndexType <- IndexType3,
  VarPType  <- VarPType3,
  VarCType  <- VarCType3,
  VarRType  <- VarRType3,
  cm        <- cm3

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
    /\ ~ fib!wellDef(I \o <<i>>)
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = fib!initCtx(i) ]                  
\*    /\ PrintT("P_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(i))

(*
   Producer ret action
*)
P_ret(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ fib!wellDef(I \o <<i>>)
    /\ fib!finished(I \o <<i>>)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> fib!out(I \o <<i>>), r |-> 0]] 
\*  /\ PrintT("P_ret" \o ToString(I \o <<i>>) 
\*                    \o " : in= "  \o ToString(fib!in(I \o <<i>>))    
\*                    \o " : ret= " \o ToString(fib!out(I \o <<i>>)))



(*
   Producer action
*)
P(I) == \/ P_call(I) /\ UNCHANGED <<cm,cm3>>
        \/ P_ret(I)  /\ UNCHANGED <<cm2,cm3>> 

(*
   Consumer call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ isPrime!wellDef(I \o <<i>>)
    /\ cm'  = [cm  EXCEPT 
         ![I].v_p[i].r = @ + 1] 
    /\ cm3' = [cm3 EXCEPT 
         ![I \o <<i>>] = isPrime!initCtx(v_p(I)[i].v) ]           
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)      
     /\ ~ written(v_c(I), i)
     /\ isPrime!wellDef(I \o <<i>>)
     /\ isPrime!finished(I \o <<i>>)   
     /\ cm' = [cm EXCEPT 
          ![I].v_c[i] = [v |-> isPrime!out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(isPrime!in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(isPrime!out(I \o <<i>>)))

(*
   Consumer action
*)
C(I) == \/ C_call(I) /\ UNCHANGED <<cm2>>
        \/ C_ret(I)  /\ UNCHANGED <<cm2,cm3>>   

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
   PCR FibPrimes6 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED <<cm2,cm3>>
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)
        \/ C(I)
        \/ R(I)    /\ UNCHANGED <<cm2,cm3>>
        \/ Quit(I) /\ UNCHANGED <<cm2,cm3>>           

=============================================================================
\* Modification History
\* Last modified Wed Dec 16 15:10:57 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
