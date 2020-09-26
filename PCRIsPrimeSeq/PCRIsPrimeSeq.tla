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
        
     PCR IsPrimeSeq(N):
       par
         p = produceSeq divisors N
         forall p
           c = consume notDivides N p
         r = reduce and (N > 1) c
   ----------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

divisors(x, p, i) == i
   
notDivides(x, p, i) == ~ (x % p[i].v = 0)

and(r1, r2) == r1 /\ r2 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)    
          
LowerBnd(x) == 2
UpperBnd(x) == Sqrt(x)
Step(i)     == IF i = 2 THEN 3 ELSE i + 2          
 
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
               ret |-> x > 1,
               ste |-> "OFF"]                      
     
Pre(x) == TRUE     
                
----------------------------------------------------------------------------                      
                                                  
(* 
   Producer action
   
   FXML:  for (i=LowerBnd(N); i < UpperBnd(N); Step(i))
            p[i] = divisors N            
   
   PCR:   p = produceSeq divisors N                              
*)
P(I) == 
  /\ Bound(I) 
  /\ map' = [map EXCEPT 
       ![I].v_p[i_p(I)] = [v |-> divisors(in(I), v_p(I), i_p(I)), r |-> 0],
       ![I].i_p         = Step(@)]         
\*  /\ PrintT("P" \o ToString(I \o <<i_p(I)>>) \o " : " \o ToString(v_p(I)[i_p(I)].v')) 


(* 
   Consumer action
   
   FXML:  forall i \in Dom(p) 
            c[i] = notDivides N p[i] 

   PCR:   c = consume notDivides N
*) 
C(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ Written(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> notDivides(in(I), v_p(I), i), r |-> 0] ]               
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))       

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce and (N > 1) c
*)
R(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_c(I), i)    
    /\ ~ Read(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].ret      = and(@, v_c(I)[i].v),
         ![I].v_c[i].r = @ + 1,
         ![I].ste      = IF CDone(I, i) THEN "END" ELSE @]                                                                     
\*    /\ IF   CDone(I, i)
\*       THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I))    
\*                       \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE       

(* 
   PCR IsPrimeSeq step at index I 
*)      
Next(I) == 
  \/ /\ State(I) = "OFF"
     /\ Start(I)
  \/ /\ State(I) = "RUN"
     /\ \/ P(I) 
        \/ C(I) 
        \/ R(I)
        \/ Quit(I)      

=============================================================================
\* Modification History
\* Last modified Sat Sep 26 16:13:07 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
