----------------------------- MODULE PCRFib --------------------------------

(*
   PCR Fib
   
   ----------------------------------------------------------
     fun fib, checkLast, projectRed
     
     lbnd projectProd = lambda x. 0 
     ubnd projectProd = lambda x. x
     
     fun fib(N,p,i) = if i < 2 then 1 else p[i-1] + p[i-2]
     fun checkLast(N,p,i) = if i < N then 0 else p[i]
     fun projectRed(r1,r2) = r1 + r2 
 
     PCR Fib(N):
       par
         p = produceSeq fib N
         forall p
           c = consume checkLast N p
         r = reduce projectRed 0 c
   ----------------------------------------------------------
*)

EXTENDS Typedef, PCRBase, TLC

VARIABLE im

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

fib(x, p, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

checkLast(x, p, i) == IF i < x THEN 0 ELSE p[i].v 

projectRed(r1, r2) == r1 + r2 

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
               v_p |-> [n \in IndexType |-> Undef],
               v_c |-> [n \in IndexType |-> Undef],
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
  /\ im' = [im  EXCEPT 
       ![I] = step(i_p(I)) ]     
\*  /\ PrintT("P" \o ToString(I \o <<i_p(I)>>) \o " : " \o ToString(v_p(I)[i_p(I)].v')) 
                                          
(* 
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = checkLast N p[j]

   PCR:   c = consume checkLast N p
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
\*    /\ ~ read(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = 1, 
         ![I].v_c[i]   = [v |-> checkLast(in(I), v_p(I), i), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce projectRed 0 c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)    
    /\ ~ read(v_c(I), i)
    /\ LET newRet == projectRed(out(I), v_c(I)[i].v)
           endSte == cDone(I, i) \/ eCnd(newRet)
       IN  cm' = [cm EXCEPT 
             ![I].ret      = newRet,
             ![I].v_c[i].r = @ + 1,
             ![I].ste      = IF endSte THEN "END" ELSE @]
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE    

(* 
   PCR Fib step at index I 
*)     
Next(I) == 
  \/ /\ state(I) = "OFF"
     /\ Start(I)
     /\ UNCHANGED im
  \/ /\ state(I) = "RUN"
     /\ \/ P(I) 
        \/ C(I)      /\ UNCHANGED im
        \/ R(I)      /\ UNCHANGED im
        \/ Quit(I)   /\ UNCHANGED im   

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 19:53:16 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
