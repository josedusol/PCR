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

isPrime(x, p, j) ==
  LET n == p[j].v
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
  /\ ~ fibRec!WellDef(i \o <<i_p(i)>>)
  /\ map2' = [map2 EXCEPT ![i \o <<i_p(i)>>] = fibRec!InitCtx(i_p(i))]              
\*  /\ PrintT("P_call" \o ToString(i \o <<i_p(i)>>) 
\*                     \o " : in= " \o ToString(i_p(i)))

(*
   Producer ret action
*)
P_ret(i) == 
  /\ ~ Written(v_p(i), i_p(i))
  /\ fibRec!WellDef(i \o <<i_p(i)>>)
  /\ fibRec!Finished(i \o <<i_p(i)>>)
  /\ map' = [map EXCEPT 
       ![i].i_p         = Step(@),
       ![i].v_p[i_p(i)] = [v |-> fibRec!Out(i \o <<i_p(i)>>), r |-> 0]]
\*  /\ PrintT("P_ret" \o ToString(i \o <<i_p(i)>>) 
\*                    \o " : in= "  \o ToString(fibRec!in(i \o <<i_p(i)>>))    
\*                    \o " : ret= " \o ToString(fibRec!Out(i \o <<i_p(i)>>)))

(*
   Producer action
*)
P(i) == \/ P_call(i) /\ UNCHANGED map
        \/ P_ret(i)  /\ UNCHANGED map2  

(* 
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = isPrime N p[j]

   PCR:   c = consume isPrime N p
*)
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = 1, 
         ![i].v_c[j]   = [v |-> isPrime(in(i), v_p(i), j), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(i \o <<j>>) \o " : P" \o ToString(j) 
\*                  \o " con v=" \o ToString(v_p(i)[j].v))

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
\*       THEN PrintT("FP4 R" \o ToString(i \o <<j>>) 
\*                           \o " : in= "  \o ToString(in(i))    
\*                           \o " : ret= " \o ToString(Out(i)')) 
\*       ELSE TRUE 


Next(i) == 
  \/ /\ State(i) = "OFF" 
     /\ Start(i)   
     /\ UNCHANGED map2
  \/ /\ State(i) = "RUN" 
     /\ \/ P(i)
        \/ C(i)    /\ UNCHANGED map2
        \/ R(i)    /\ UNCHANGED map2
        \/ Quit(i) /\ UNCHANGED map2           

=============================================================================
\* Modification History
\* Last modified Fri Sep 25 02:38:52 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
