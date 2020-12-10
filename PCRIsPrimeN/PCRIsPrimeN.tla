--------------------------- MODULE PCRIsPrimeN ----------------------------

(*
   PCR IsPrimeN
   
   This is an experimental alternative version where we use base modules
   that works with arbitrary number of consumers.
   
   ----------------------------------------------------------
     fun divisors, notDivides, and
     
     lbnd divisors = lambda x. 2 
     ubnd divisors = lambda x. Sqrt(x)
     step divisors = lambda x. if x == 2 then 3 else x+2
     
     fun divisors(N,p,i) = i
     fun notDivides(N,p,i) = not (N % p[I] == 0)
     fun and(r,z) = r && z 
        
     PCR IsPrime(N):
       par
         p = produce divisors N
         forall p
           c = consume notDivides N p
         r = reduce and (N > 1) c
   ----------------------------------------------------------
*)

EXTENDS PCRIsPrimeNTypes, PCRBaseN, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

divisors(x, p, i) == i
   
notDivides(x, p, i) == ~ (x % p[i].v = 0)

and(r, z) == r /\ z 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)    
          
lowerBnd(x) == 2
upperBnd(x) == Sqrt(x)
step(i)     == IF i = 2 THEN 3 ELSE i + 2          
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpaceN WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)
                      
initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> <<[i \in IndexType |-> Undef]>>,
               ret |-> x > 1,
               ste |-> "OFF"]                      
     
pre(x) == TRUE
                
----------------------------------------------------------------------------                      
                                                  
(* 
   Producer action
   
   FXML:  forall i \in Range(2,Sqrt(N),Step)
            p[i] = divisors N               
   
   PCR:   p = produce divisors N
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> divisors(in(I), v_p(I), i), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))  

(* 
   Consumer action
   
   FXML:  forall i \in Dom(p) 
            c[i] = notDivides N p[i] 

   PCR:   c = consume notDivides N
*) 
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(1,I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r  = @ + 1,
         ![I].v_c[1][i] = [v |-> notDivides(in(I), v_p(I), i), r |-> 0] ]               
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))       

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce and (N > 1) c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(1,I), i)    
    /\ ~ read(v_c(1,I), i)   
    /\ LET newRet == and(out(I), v_c(1,I)[i].v)
           endSte == cDone(I, i) \/ eCnd(newRet)
       IN  cm' = [cm EXCEPT 
             ![I].ret         = newRet,
             ![I].v_c[1][i].r = @ + 1,
             ![I].ste         = IF endSte THEN "END" ELSE @]                                                                               
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE       

(* 
   PCR IsPrime step at index I 
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
\* Last modified Wed Nov 18 21:02:09 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed