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

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

VARIABLES i_p, map2, i_p2

----------------------------------------------------------------------------

(* 
   Basic functions                          
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

sum(r1, r2) == r1 + (IF r2 THEN 1 ELSE 0)  

isPrime == INSTANCE PCRIsPrime WITH
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  map       <- map2,
  i_p       <- i_p2

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
\*               v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
\*               v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               v_p |-> [n \in IndexType |-> Undef],
               v_c |-> [n \in IndexType |-> Undef],
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
  /\ bound(I) 
  /\ map' = [map EXCEPT 
       ![I].v_p[i_p] = [v |-> fib(in(I), v_p(I), i_p), r |-> 0] ]
\*       ![I].i_p      = Step(@)] 
  /\ i_p' = Step(i_p)              
\*  /\ PrintT("P" \o ToString(I \o <<i_p(I)>>) \o " : " \o ToString(v_p(I)[i_p(I)].v'))

(*
   Consumer call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ map'  = [map  EXCEPT ![I].v_p[i].r = 1] 
    /\ map2' = [map2 EXCEPT 
         ![I \o <<i>>] = isPrime!InitCtx(v_p(I)[i].v)] 
    /\ i_p2' = isPrime!LowerBnd(v_p(I)[i].v)        
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
     /\ isPrime!finished(I \o <<i>>)   
     /\ map' = [map EXCEPT 
          ![I].v_c[i]= [v |-> isPrime!out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(isPrime!in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(isPrime!Out(I \o <<i>>)))

(*
   Consumer action
*)
C(I) == \/ C_call(I) 
        \/ C_ret(I) /\ UNCHANGED <<map2,i_p2>>   

(* 
   Reducer action
   
   FXML:  ... 

   PCR:   r = reduce sum 0 c
*)
R(I) == 
  \E i \in iterator(I) :
     /\ written(v_c(I), i)  
     /\ ~ read(v_c(I), i)
     /\ map' = [map EXCEPT 
          ![I].ret      = sum(@, v_c(I)[i].v),
          ![I].v_c[i].r = @ + 1,
          ![I].ste      = IF cDone(I, i) THEN "END" ELSE @] 
\*    /\ IF   CDone(I, i)
\*       THEN PrintT("FP2 R" \o ToString(I \o <<i>>) 
\*                           \o " : in= "  \o ToString(in(I))    
\*                           \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE 

(* 
   PCR FibPrimes2 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED <<i_p,map2,i_p2>>
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)      /\ UNCHANGED <<map2,i_p2>>
        \/ C(I)      /\ UNCHANGED i_p
        \/ R(I)      /\ UNCHANGED <<i_p,map2,i_p2>>
        \/ Eureka(I) /\ UNCHANGED <<i_p,map2,i_p2>>
        \/ Quit(I)   /\ UNCHANGED <<i_p,map2,i_p2>>           

=============================================================================
\* Modification History
\* Last modified Wed Sep 30 01:32:16 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
