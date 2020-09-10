-------------------------- MODULE PCRFibPrimes2 ----------------------------

(*
   PCR FibPrimes2
   
   ----------------------------------------------------------
     fun fib, sum
   
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

VARIABLE map2

InitCtx(input) == [in  |-> input,
                   i_p |-> LowerBnd(input),
                   v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   ret |-> 0,
                   ste |-> OFF]

----------------------------------------------------------------------------

(* 
   Basic functions that should be defined in host language                            
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

sum(old, new) == old + (IF new THEN 1 ELSE 0)  

isPrime == INSTANCE PCRIsPrime WITH
  InType    <- InType2,
  LowerBnd  <- LAMBDA x : 2,
  UpperBnd  <- LAMBDA x : Sqrt(x),  
  Step      <- LAMBDA x : 2*x - 1,  
  IndexType <- IndexType2,
  CtxIdType <- CtxIdType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  map       <- map2

----------------------------------------------------------------------------

(* 
   Producer action
   
   FXML:  for (j=LowerBnd(N); j < UpperBnd(N); Step(j))
            p[j] = fib N            
   
   PCR:   p = produceSeq fib N                              
*)
P(i) == 
  /\ Bound(i) 
  /\ map' = [map EXCEPT 
       ![i].v_p[i_p(i)] = [v |-> fib(in(i), v_p(i), i_p(i)), r |-> 0],
       ![i].i_p         = Step(@)]         
\*  /\ PrintT("P" \o ToString(j) \o " : " \o ToString(v_p(i)[j].v'))           

(*
   Consumer call action
*)
C_call(i) == 
  \E j \in Iterator(i):
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ map'  = [map  EXCEPT ![i].v_p[j].r = 1] 
    /\ map2' = [map2 EXCEPT 
         ![i \o <<j>>] = isPrime!InitCtx(v_p(i)[j].v)]    
\*    /\ PrintT("C_call " \o ToString(i \o <<j>>) 
\*                        \o " : in= " \o ToString(v_p(i)[j].v))                                                                                                                                            

(*
   Consumer end action
*)
C_ret(i) == 
  /\ \E j \in Iterator(i) :
       /\ Read(v_p(i), j)       
       /\ ~ Written(v_c(i), j)
       /\ isPrime!Finished(i \o <<j>>)   
       /\ map' = [map EXCEPT 
            ![i].v_c[j]= [v |-> isPrime!Out(i \o <<j>>), r |-> 0]]  
\*       /\ PrintT("C_ret" \o ToString(i \o <<j>>) 
\*                         \o " : in= "  \o ToString(isPrime!in(i \o <<j>>))    
\*                         \o " : ret= " \o ToString(isPrime!Out(i \o <<j>>)))                

(*
   Consumer action
*)
C(i) == \/ C_call(i) 
        \/ C_ret(i) /\ UNCHANGED map2   

(* 
   Reducer action
   
   FXML:  forall i \in Dom(v_p)
            r[j+1] = r[j] + count W i 

   PCR:   r = reduce joinCounts {} v_c
*)
R(i) == 
  /\ \E j \in Iterator(i) :
       /\ Written(v_c(i), j)  
       /\ ~ Read(v_c(i), j)
       /\ map' = [map EXCEPT 
            ![i].ret      = sum(@, v_c(i)[j].v),
            ![i].v_c[j].r = @ + 1,
            ![i].ste      = IF CDone(i, j) THEN END ELSE @]                                                                 
\*       /\ IF CDone(i, j)
\*          THEN PrintT("FP: in= " \o ToString(in(i)) 
\*                                 \o " ret= " \o ToString(Out(i)'))
\*          ELSE TRUE                
           
Next(i) == 
  \/ /\ Off(i) 
     /\ Start(i)   
     /\ UNCHANGED map2
  \/ /\ Running(i) 
     /\ \/ P(i)    /\ UNCHANGED map2
        \/ C(i)  
        \/ R(i)    /\ UNCHANGED map2
        \/ Quit(i) /\ UNCHANGED map2           

=============================================================================
\* Modification History
\* Last modified Wed Sep 09 20:11:56 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
