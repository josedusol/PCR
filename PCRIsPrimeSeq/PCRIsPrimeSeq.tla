-------------------------- MODULE PCRIsPrimeSeq ----------------------------

(*
   PCR IsPrimeSeq
   
   ----------------------------------------------------------
     fun divisors, notDivides, and
     
     lbnd divisors = lambda x. 2 
     ubnd divisors = lambda x. Sqrt(x)
     step divisors = lambda x. if x == 2 then 3 else x+2
     
     fun divisors(N,p,i) = i
     fun notDivides(N,p,i) = not (N % p[i] == 0)
     fun and(r1,r2) = r1 && r2 
        
     dep p(i-1) -> p(i)   
        
     PCR IsPrimeSeq(N):
       par
         p = produce divisors N
         forall p
           c = consume notDivides N p
         r = reduce and (N > 1) c
   ----------------------------------------------------------
*)

EXTENDS PCRIsPrimeSeqTypes, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

divisors(x, p, I, i) == i
   
notDivides(x, p, I, i) == ~ (x % p[i].v = 0)

and(x, o, c, I, i) == o /\ c[i].v 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)    
          
lowerBnd(x) == 2
upperBnd(x) == Sqrt(x)
step(i)     == IF i = 2 THEN 3 ELSE i + 2          
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpace WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

r0(x) == [v |-> x > 1, r |-> 0]

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
   
   PCR:  p = produce divisors N
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ i > lowerBnd(in(I)) => written(v_p(I), i-1)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> divisors(in(I), v_p(I), I, i), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))

(* 
   Consumer action
   
   PCR:  c = consume notDivides N
*) 
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> notDivides(in(I), v_p(I), I, i), r |-> 0] ]               
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))       

(* 
   Reducer action
   
   PCR:  c = reduce and (N > 1) c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == and(in(I), out(I), v_c(I), I, i)
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
   PCR IsPrimeSeq step at index I 
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
\* Last modified Wed Dec 16 14:57:56 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
