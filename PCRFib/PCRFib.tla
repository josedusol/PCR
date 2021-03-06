----------------------------- MODULE PCRFib --------------------------------

(*
   PCR Fib
   
   ----------------------------------------------------------
     fun fib, checkLast, projectRed
     
     lbnd projectProd = lambda x. 0 
     ubnd projectProd = lambda x. x
     
     fun fib(N,p,i) = if i < 2 then 1 else p[i-1] + p[i-2]
     fun checkLast(N,p,i) = if i < N then 0 else p[i]
     fun projectRed(N,o,c,i) = o + c[i] 
 
     dep p(i-1) -> p(i)
     dep p(i-2) -> p(i)
 
     PCR Fib(N):
       par
         p = produce fib N
         forall p
           c = consume checkLast N p
         r = reduce projectRed 0 c
   ----------------------------------------------------------
*)

EXTENDS PCRFibTypes, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

fib(x, p, I, i) == IF i < 2 THEN 1 ELSE p[i-1].v + p[i-2].v

checkLast(x, p, I, i) == IF i < x THEN 0 ELSE p[i].v 

projectRed(x, o, c, I, i) == o + c[i].v 

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
   
   PCR:  p = produce fib N                              
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ i > lowerBnd(in(I))     => written(v_p(I), i-1)
    /\ i > lowerBnd(in(I)) + 1 => written(v_p(I), i-2)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> fib(in(I), v_p(I), I, i), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))
                                     
(* 
   Consumer action

   PCR:  c = consume checkLast N p
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = 1, 
         ![I].v_c[i]   = [v |-> checkLast(in(I), v_p(I), I, i), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  

(* 
   Reducer action

   PCR:  c = reduce projectRed 0 c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == projectRed(in(I), out(I), v_c(I), I, i)
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
   PCR Fib step at index I 
*)     
Next(I) == 
  \/ /\ state(I) = "OFF"
     /\ Start(I)
  \/ /\ state(I) = "RUN"
     /\ \/ P(I) 
        \/ C(I)
        \/ R(I)
        \/ Quit(I) 

=============================================================================
\* Modification History
\* Last modified Wed Dec 16 15:12:40 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
