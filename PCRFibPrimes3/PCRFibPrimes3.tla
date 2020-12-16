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

EXTENDS PCRFibPrimes3Types, PCRBase, TLC

VARIABLE cm2, im

----------------------------------------------------------------------------

(* 
   Basic functions                          
*)

fib(x, p, I, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

sum(x, o, c, I, i) == o + (IF c[i].v THEN 1 ELSE 0)  

isPrimeRec == INSTANCE PCRIsPrimeRec WITH
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
   Producer action
   
   FXML:  for (i=LowerBnd(N); i < UpperBnd(N); Step(i))
            p[i] = fib N            
   
   PCR:   p = produceSeq fib N                              
*)
P(I) == 
  /\ i_p(I) \in iterator(I) 
  /\ cm' = [cm EXCEPT 
       ![I].v_p[i_p(I)] = [v |-> fib(in(I), v_p(I), I, i_p(I)), r |-> 0]]     
  /\ im' = [im EXCEPT 
       ![I] = step(i_p(I))]         
\*  /\ PrintT("P" \o ToString(i \o <<i_p(I)>>) \o " : " \o ToString(v_p(I)[i_p(I)].v'))

(*
   Consumer call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ isPrimeRec!wellDef(I \o <<i>>)
    /\ cm'  = [cm  EXCEPT 
         ![I].v_p[i].r = @ + 1] 
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = isPrimeRec!initCtx(<<v_p(I)[i].v, Sqrt(v_p(I)[i].v)>>)]    
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in1= " \o ToString(isPrimeRec!in1(I \o <<i>>)')      
\*                       \o " : in2= " \o ToString(isPrimeRec!in2(I \o <<i>>)'))                                                                                                                                        

(*
   Consumer end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)        
    /\ ~ written(v_c(I), i)
    /\ isPrimeRec!wellDef(I \o <<i>>)  
    /\ isPrimeRec!finished(I \o <<i>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i]= [v |-> isPrimeRec!out(I \o <<i>>), r |-> 0]]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                      \o " : in1= " \o ToString(isPrimeRec!in1(I \o <<i>>)) 
\*                      \o " : in2= " \o ToString(isPrimeRec!in2(I \o <<i>>))   
\*                      \o " : ret= " \o ToString(isPrimeRec!out(I \o <<i>>)))

(*
   Consumer action
*)
C(I) == \/ C_call(I) /\ UNCHANGED im
        \/ C_ret(I)  /\ UNCHANGED <<cm2,im>>   

(* 
   Reducer action
   
   FXML:  ...

   PCR:   c = reduce sum 0 c
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
   PCR FibPrimes3 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED <<cm2,im>> 
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED cm2 
        \/ C(I)  
        \/ R(I)    /\ UNCHANGED <<cm2,im>> 
        \/ Quit(I) /\ UNCHANGED <<cm2,im>>            

=============================================================================
\* Modification History
\* Last modified Tue Dec 15 20:54:02 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
