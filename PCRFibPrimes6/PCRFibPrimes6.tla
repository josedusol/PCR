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
Step(j)     == j + 1  

INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step

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
P_call(i) == 
  /\ Bound(i) 
  /\ ~ fib!WellDef(i \o <<i_p(i)>>)
  /\ map2' = [map2 EXCEPT ![i \o <<i_p(i)>>] = fib!InitCtx(i_p(i))]              
\*  /\ PrintT("P_call" \o ToString(i \o <<i_p(i)>>) 
\*                     \o " : in= " \o ToString(i_p(i)))

(*
   Producer ret action
*)
P_ret(i) == 
  /\ ~ Written(v_p(i), i_p(i))
  /\ fib!WellDef(i \o <<i_p(i)>>)
  /\ fib!Finished(i \o <<i_p(i)>>)
  /\ map' = [map EXCEPT 
       ![i].i_p         = Step(@),
       ![i].v_p[i_p(i)] = [v |-> fib!Out(i \o <<i_p(i)>>), r |-> 0]]
\*  /\ PrintT("P_ret" \o ToString(i \o <<i_p(i)>>) 
\*                    \o " : in= "  \o ToString(fib!in(i \o <<i_p(i)>>))    
\*                    \o " : ret= " \o ToString(fib!Out(i \o <<i_p(i)>>)))

(*
   Producer action
*)
P(i) == \/ P_call(i) /\ UNCHANGED <<map,map3>>
        \/ P_ret(i)  /\ UNCHANGED <<map2,map3>> 

(*
   Consumer call action
*)
C_call(i) == 
  \E j \in Iterator(i):
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ map'  = [map  EXCEPT ![i].v_p[j].r = 1] 
    /\ map3' = [map3 EXCEPT 
         ![i \o <<j>>] = isPrime!InitCtx(v_p(i)[j].v)]    
\*    /\ PrintT("C_call" \o ToString(i \o <<j>>) 
\*                       \o " : in= " \o ToString(v_p(i)[j].v))                                                                                                                                            

(*
   Consumer end action
*)
C_ret(i) == 
  \E j \in Iterator(i) :
     /\ Read(v_p(i), j)       
     /\ ~ Written(v_c(i), j)
     /\ isPrime!Finished(i \o <<j>>)   
     /\ map' = [map EXCEPT 
          ![i].v_c[j]= [v |-> isPrime!Out(i \o <<j>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(i \o <<j>>) 
\*                       \o " : in= "  \o ToString(isPrime!in(i \o <<j>>))    
\*                       \o " : ret= " \o ToString(isPrime!Out(i \o <<j>>)))

(*
   Consumer action
*)
C(i) == \/ C_call(i) /\ UNCHANGED map2
        \/ C_ret(i)  /\ UNCHANGED <<map2,map3>>   

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
          ![i].ste      = IF CDone(i, j) THEN "END" ELSE @] 
\*    /\ IF   CDone(i, j)
\*       THEN PrintT("FP6 R" \o ToString(i \o <<j>>) 
\*                           \o " : in= "  \o ToString(in(i))    
\*                           \o " : ret= " \o ToString(Out(i)')) 
\*       ELSE TRUE 


Next(i) == 
  \/ /\ State(i) = "OFF" 
     /\ Start(i)   
     /\ UNCHANGED <<map2,map3>>
  \/ /\ State(i) = "RUN" 
     /\ \/ P(i)
        \/ C(i)
        \/ R(i)    /\ UNCHANGED <<map2,map3>>
        \/ Quit(i) /\ UNCHANGED <<map2,map3>>           

=============================================================================
\* Modification History
\* Last modified Fri Sep 25 14:32:50 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
