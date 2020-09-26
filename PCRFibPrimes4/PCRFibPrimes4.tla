-------------------------- MODULE PCRFibPrimes4 ----------------------------

(*
   PCR FibPrimes4
   
   ----------------------------------------------------------
     fun isPrime, sum
   
     lbnd fib = lambda x. 0 
     ubnd fib = lambda x. x
     step fib = lambda x. x + 1
   
     fun sum(r1,r2) = r1 + (if r2 then 1 else 0)  
   
     PCR FibPrimes4(N):
       par
         p = produceSeq fibRec p     \\ call fibRec PCR as a function
         forall p
           c = consume isPrime N p
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

isPrime(x, p, i) ==
  LET n == p[i].v
      F[d \in Nat] ==
        IF d < 2
        THEN n > 1
        ELSE ~ (n % d = 0) /\ F[d-1]
  IN F[Sqrt(n)]

sum(r1, r2) == r1 + (IF r2 THEN 1 ELSE 0)  

fibRec == INSTANCE PCRFibRec WITH
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
   Producer call action
*)
P_call(I) == 
  /\ Bound(I) 
  /\ ~ fibRec!WellDef(I \o <<i_p(I)>>)
  /\ map2' = [map2 EXCEPT ![I \o <<i_p(I)>>] = fibRec!InitCtx(i_p(I))]              
\*  /\ PrintT("P_call" \o ToString(I \o <<i_p(I)>>) 
\*                     \o " : in= " \o ToString(i_p(I)))

(*
   Producer ret action
*)
P_ret(I) == 
  /\ ~ Written(v_p(I), i_p(I))
  /\ fibRec!WellDef(I \o <<i_p(I)>>)
  /\ fibRec!Finished(I \o <<i_p(I)>>)
  /\ map' = [map EXCEPT 
       ![I].i_p         = Step(@),
       ![I].v_p[i_p(I)] = [v |-> fibRec!Out(I \o <<i_p(I)>>), r |-> 0]]
\*  /\ PrintT("P_ret" \o ToString(I \o <<i_p(I)>>) 
\*                    \o " : in= "  \o ToString(fibRec!in(I \o <<i_p(I)>>))    
\*                    \o " : ret= " \o ToString(fibRec!Out(I \o <<i_p(I)>>)))

(*
   Producer action
*)
P(I) == \/ P_call(I) /\ UNCHANGED map
        \/ P_ret(I)  /\ UNCHANGED map2  

(* 
   Consumer action
   
   FXML:  forall i \in Dom(p)
            c[i] = isPrime N p[i]

   PCR:   c = consume isPrime N p
*)
C(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ Written(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r = 1, 
         ![I].v_c[i]   = [v |-> isPrime(in(I), v_p(I), i), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))

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
\*       THEN PrintT("FP4 R" \o ToString(I \o <<i>>) 
\*                           \o " : in= "  \o ToString(in(I))    
\*                           \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE 

(* 
   PCR FibPrimes4 step at index I 
*)
Next(I) == 
  \/ /\ State(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED map2
  \/ /\ State(I) = "RUN" 
     /\ \/ P(I)
        \/ C(I)    /\ UNCHANGED map2
        \/ R(I)    /\ UNCHANGED map2
        \/ Quit(I) /\ UNCHANGED map2           

=============================================================================
\* Modification History
\* Last modified Sat Sep 26 16:04:37 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
