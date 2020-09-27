-------------------------- MODULE PCRFibPrimes6 ----------------------------

(*
   PCR FibPrimes6
   
   ----------------------------------------------------------
     fun sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun sum(r1,r2) = r1 + (if r2 then 1 else 0)  
   
     PCR FibPrimes6(N):
       par
         p = produceSeq fib p     \\ call fib PCR as a function
         forall p
           c = consume isPrime p  \\ call isPrime PCR as a function
         r = reduce sum 0 c
   ----------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

VARIABLES map2, map3

----------------------------------------------------------------------------

(* 
   Basic functions                          
*)

sum(r1, r2) == r1 + (IF r2 THEN 1 ELSE 0)  

fib == INSTANCE PCRFib WITH
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  map       <- map2

isPrime == INSTANCE PCRIsPrime WITH
  InType    <- InType3,
  CtxIdType <- CtxIdType3,
  IndexType <- IndexType3,
  VarPType  <- VarPType3,
  VarCType  <- VarCType3,
  VarRType  <- VarRType3,
  map       <- map3

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
  ECnd      <- ECnd

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

InitCtx(x) == [in  |-> x,
               i_p |-> LowerBnd(x),
               v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               ret |-> 0,
               ste |-> "OFF"]

Pre(x) == TRUE

----------------------------------------------------------------------------

(*
   Producer call action
*)
P_call(I) == 
  /\ Bound(I) 
  /\ ~ fib!WellDef(I \o <<i_p(I)>>)
  /\ map2' = [map2 EXCEPT ![I \o <<i_p(I)>>] = fib!InitCtx(i_p(I))]              
\*  /\ PrintT("P_call" \o ToString(I \o <<i_p(I)>>) 
\*                     \o " : in= " \o ToString(i_p(I)))

(*
   Producer ret action
*)
P_ret(I) == 
  /\ ~ Written(v_p(I), i_p(I))
  /\ fib!WellDef(I \o <<i_p(I)>>)
  /\ fib!Finished(I \o <<i_p(I)>>)
  /\ map' = [map EXCEPT 
       ![I].i_p         = Step(@),
       ![I].v_p[i_p(I)] = [v |-> fib!Out(I \o <<i_p(I)>>), r |-> 0]]
\*  /\ PrintT("P_ret" \o ToString(I \o <<i_p(I)>>) 
\*                    \o " : in= "  \o ToString(fib!in(I \o <<i_p(I)>>))    
\*                    \o " : ret= " \o ToString(fib!Out(I \o <<i_p(I)>>)))

(*
   Producer action
*)
P(I) == \/ P_call(I) /\ UNCHANGED <<map,map3>>
        \/ P_ret(I)  /\ UNCHANGED <<map2,map3>> 

(*
   Consumer call action
*)
C_call(I) == 
  \E i \in Iterator(I):
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ map'  = [map  EXCEPT ![I].v_p[i].r = 1] 
    /\ map3' = [map3 EXCEPT 
         ![I \o <<i>>] = isPrime!InitCtx(v_p(I)[i].v)]    
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer end action
*)
C_ret(I) == 
  \E i \in Iterator(I) :
     /\ Read(v_p(I), i)       
     /\ ~ Written(v_c(I), i)
     /\ isPrime!Finished(I \o <<i>>)   
     /\ map' = [map EXCEPT 
          ![I].v_c[i]= [v |-> isPrime!Out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(isPrime!in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(isPrime!Out(I \o <<i>>)))

(*
   Consumer action
*)
C(I) == \/ C_call(I) /\ UNCHANGED map2
        \/ C_ret(I)  /\ UNCHANGED <<map2,map3>>   

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
\*    /\ IF   CDone(i, j)
\*       THEN PrintT("FP6 R" \o ToString(I \o <<j>>) 
\*                           \o " : in= "  \o ToString(in(I))    
\*                           \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE 

(* 
   PCR FibPrimes6 step at index I 
*)
Next(I) == 
  \/ /\ State(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED <<map2,map3>>
  \/ /\ State(I) = "RUN" 
     /\ \/ P(I)
        \/ C(I)
        \/ R(I)      /\ UNCHANGED <<map2,map3>>
        \/ Eureka(I) /\ UNCHANGED <<map2,map3>>
        \/ Quit(I)   /\ UNCHANGED <<map2,map3>>           

=============================================================================
\* Modification History
\* Last modified Sun Sep 27 16:07:15 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
