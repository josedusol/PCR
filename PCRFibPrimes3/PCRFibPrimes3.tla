-------------------------- MODULE PCRFibPrimes3 ----------------------------

(*
   PCR FibPrimes3
   
   ----------------------------------------------------------
     fun fib, sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun fib(N,p,i) = if i < 2 then 1 else p[i-1] + p[i-2]
     fun sum(a,b) = a + (if b then 1 else 0)  
   
     PCR FibPrimes3(N):
       par
         p = produceSeq fib N
         forall p
           c = consume isPrimeRec p Sqrt(p)   \\ call isPrimeRec PCR as a function
         r = reduce sum 0 c
   ----------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

VARIABLE map2

----------------------------------------------------------------------------

(* 
   Basic functions                          
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

sum(r1, r2) == r1 + (IF r2 THEN 1 ELSE 0)  

isPrimeRec == INSTANCE PCRIsPrimeRec WITH
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  map       <- map2

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 0
UpperBnd(x) == x
Step(i)     == i + 1  

INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step

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
   Producer action
   
   FXML:  for (i=LowerBnd(N); i < UpperBnd(N); Step(i))
            p[i] = fib N            
   
   PCR:   p = produceSeq fib N                              
*)
P(I) == 
  /\ Bound(I) 
  /\ map' = [map EXCEPT 
       ![I].v_p[i_p(I)] = [v |-> fib(in(I), v_p(I), i_p(I)), r |-> 0],
       ![I].i_p         = Step(@)]         
\*  /\ PrintT("P" \o ToString(i \o <<i_p(I)>>) \o " : " \o ToString(v_p(I)[i_p(I)].v'))

(*
   Consumer call action
*)
C_call(I) == 
  \E i \in Iterator(I):
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ map'  = [map  EXCEPT ![I].v_p[i].r = 1] 
    /\ map2' = [map2 EXCEPT 
         ![I \o <<i>>] = isPrimeRec!InitCtx(<<v_p(I)[i].v, Sqrt(v_p(I)[i].v)>>)]    
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in1= " \o ToString(isPrimeRec!In1(I \o <<i>>)')      
\*                       \o " : in2= " \o ToString(isPrimeRec!In2(I \o <<i>>)'))                                                                                                                                        

(*
   Consumer end action
*)
C_ret(I) == 
  \E i \in Iterator(I) :
     /\ Read(v_p(I), i)       
     /\ ~ Written(v_c(I), i)
     /\ isPrimeRec!Finished(I \o <<i>>)   
     /\ map' = [map EXCEPT 
          ![I].v_c[i]= [v |-> isPrimeRec!Out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in1= " \o ToString(isPrimeRec!In1(I \o <<i>>)) 
\*                       \o " : in2= " \o ToString(isPrimeRec!In2(I \o <<i>>))   
\*                       \o " : ret= " \o ToString(isPrimeRec!Out(I \o <<i>>)))

(*
   Consumer action
*)
C(I) == \/ C_call(I) 
        \/ C_ret(I) /\ UNCHANGED map2   

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
\*    /\ IF   CDone(I, i)
\*       THEN PrintT("FP2 R" \o ToString(I \o <<i>>) 
\*                           \o " : in= "  \o ToString(in(I))    
\*                           \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE 

(* 
   PCR FibPrimes3 step at index I 
*)
Next(I) == 
  \/ /\ State(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED map2
  \/ /\ State(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED map2
        \/ C(I)  
        \/ R(I)    /\ UNCHANGED map2
        \/ Quit(I) /\ UNCHANGED map2           

=============================================================================
\* Modification History
\* Last modified Sat Sep 26 16:04:24 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
