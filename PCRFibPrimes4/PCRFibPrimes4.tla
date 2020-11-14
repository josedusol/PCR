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

EXTENDS PCRFibPrimes4Types, PCRBase, TLC

VARIABLES cm2, im

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
  cm        <- cm2

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == x
step(i)     == i + 1  
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpaceSeq WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

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
   Producer call action
*)
P_call(I) == 
  /\ i_p(I) \in iterator(I)  
  /\ ~ fibRec!wellDef(I \o <<i_p(I)>>)
  /\ cm2' = [cm2 EXCEPT 
       ![I \o <<i_p(I)>>] = fibRec!initCtx(i_p(I)) ]                  
\*  /\ PrintT("P_call" \o ToString(I \o <<i_p(I)>>) 
\*                     \o " : in= " \o ToString(i_p(I)))

(*
   Producer ret action
*)
P_ret(I) == 
  /\ i_p(I) \in iterator(I)
  /\ ~ written(v_p(I), i_p(I))
  /\ fibRec!wellDef(I \o <<i_p(I)>>)
  /\ fibRec!finished(I \o <<i_p(I)>>)
  /\ cm' = [cm EXCEPT 
       ![I].v_p[i_p(I)] = [v |-> fibRec!out(I \o <<i_p(I)>>), r |-> 0]]
  /\ im'  = [im  EXCEPT 
       ![I] = step(i_p(I)) ]     
\*  /\ PrintT("P_ret" \o ToString(I \o <<i_p(I)>>) 
\*                    \o " : in= "  \o ToString(fibRec!in(I \o <<i_p(I)>>))    
\*                    \o " : ret= " \o ToString(fibRec!out(I \o <<i_p(I)>>)))

(*
   Producer action
*)
P(I) == \/ P_call(I) /\ UNCHANGED <<cm,im>>
        \/ P_ret(I)  /\ UNCHANGED cm2  

(* 
   Consumer action
   
   FXML:  forall i \in Dom(p)
            c[i] = isPrime N p[i]

   PCR:   c = consume isPrime N p
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> isPrime(in(I), v_p(I), i), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))

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
\*          /\ IF   endSte
\*             THEN PrintT("FP4 R" \o ToString(I \o <<i>>) 
\*                                 \o " : in= "  \o ToString(in(I))    
\*                                 \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE 

(* 
   PCR FibPrimes4 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED <<cm2,im>>
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)
        \/ C(I)      /\ UNCHANGED <<cm2,im>>
        \/ R(I)      /\ UNCHANGED <<cm2,im>>
        \/ Quit(I)   /\ UNCHANGED <<cm2,im>>           

=============================================================================
\* Modification History
\* Last modified Tue Nov 10 23:30:55 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
