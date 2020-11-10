-------------------------- MODULE PCRFibPrimes2 ----------------------------

(*
   PCR FibPrimes2
   
   ----------------------------------------------------------
     fun fib, sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun fib(N,p,i) = if i < 2 then 1 else p[i-1] + p[i-2]
     fun sum(r1,r2) = r1 + (if r2 then 1 else 0)  
   
     PCR FibPrimes2(N):
       par
         p = produceSeq fib N
         forall p
           c = consume isPrime p   \\ call isPrime PCR as a function
         r = reduce sum 0 c
   ----------------------------------------------------------
*)

EXTENDS PCRFibPrimes2Types, PCRBase, TLC

VARIABLES cm2, im

----------------------------------------------------------------------------

(* 
   Basic functions                          
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

sum(r1, r2) == r1 + (IF r2 THEN 1 ELSE 0)  

PCRisPrime == INSTANCE PCRIsPrime WITH
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

i_p(I)   == im[I]
IndexMap == [CtxIdType -> IndexType \union {Undef}] 
  
----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
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
       ![I].v_p[i_p(I)] = [v |-> fib(in(I), v_p(I), i_p(I)), r |-> 0] ]
  /\ im' = [im EXCEPT 
       ![I] = step(i_p(I))]   
\*  /\ PrintT("P" \o ToString(I \o <<i_p(I)>>) \o " : " \o ToString(v_p(I)[i_p(I)].v'))

(*
   Consumer call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ cm'  = [cm  EXCEPT 
         ![I].v_p[i].r = @ + 1] 
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = PCRisPrime!initCtx(v_p(I)[i].v) ]   
\*    /\ PrintT("C_call" \o ToString(I \o <<j>>) 
\*                       \o " : in= " \o ToString(v_p(I)[j].v))                                                                                                                                            

(*
   Consumer end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)       
    /\ ~ written(v_c(I), i)
    /\ PCRisPrime!wellDef(I \o <<i>>) 
    /\ PCRisPrime!finished(I \o <<i>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> PCRisPrime!out(I \o <<i>>), r |-> 0]]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(isPrime!in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(isPrime!Out(I \o <<i>>)))

(*
   Consumer action
*)
C(I) == \/ C_call(I) /\ UNCHANGED im
        \/ C_ret(I)  /\ UNCHANGED <<cm2,im>>   

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
\*             THEN PrintT("FP2 R" \o ToString(I \o <<i>>) 
\*                                 \o " : in= "  \o ToString(in(I))    
\*                                 \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE 

(* 
   PCR FibPrimes2 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED <<cm2,im>> 
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)      /\ UNCHANGED <<cm2>>
        \/ C(I)
        \/ R(I)      /\ UNCHANGED <<cm2,im>> 
        \/ Quit(I)   /\ UNCHANGED <<cm2,im>>            

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 02:46:45 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
