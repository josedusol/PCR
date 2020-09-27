-------------------------- MODULE PCRFirstEven -----------------------------

(*
   PCR FirstEven
   
   ----------------------------------------------------------
     fun id, checkEven, reducer
     
     lbnd projectProd = lambda x. 0 
     ubnd projectProd = lambda x. x
     
     fun id(N,p,i) = i
     fun checkEven(N,p,i) = if (p[i] % 2 = 0) 
                            then p[i] 
                            else 1
     fun reducer(r1,r2) = if not (r2 = 1)
                          then r2
                          else r1  
     PCR FirstEven(N):
       par
         p = produce id N
         forall p
           c = consume checkEven N p
         r = reduce reducer 0 c
   ----------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

id(x, p, i) == i

checkEven(x, p, i) == IF p[i].v % 2 = 0 THEN p[i].v ELSE 1

reducer(r1, r2) == IF r2 # 1 THEN r2 ELSE r1

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 0
UpperBnd(x) == x
Step(i)     == i + 1
ECnd(r)     == r % 2 = 0
\*ECnd(r)     == FALSE
 
INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step,
  ECnd      <- ECnd

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
   Producer action
   
   FXML:  forall i \in Range(0,N,Step)
            p[i] = id N               
   
   PCR:   p = produce id N
*)
P(I) == 
  \E i \in Iterator(I) :
    /\ ~ Written(v_p(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i] = [v |-> id(in(I), v_p(I), i), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))
                                          
(* 
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = checkEven N p[j]

   PCR:   c = consume checkEven N p
*)
C(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ Written(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r = 1, 
         ![I].v_c[i]   = [v |-> checkEven(in(I), v_p(I), i), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce reducer 0 c
*)
R(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_c(I), i)    
    /\ ~ Read(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].ret      = reducer(@, v_c(I)[i].v),
         ![I].v_c[i].r = @ + 1,
         ![I].ste      = IF CDone(I, i) THEN "END" ELSE @]
\*    /\ IF   CDone(I, i)
\*       THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I))    
\*                       \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE    

(* 
   PCR FirstEven step at index I 
*)     
Next(I) == 
  \/ /\ State(I) = "OFF"
     /\ Start(I)
  \/ /\ State(I) = "RUN"
     /\ \/ P(I) 
        \/ C(I) 
        \/ R(I)
        \/ Eureka(I)
        \/ Quit(I)      

=============================================================================
\* Modification History
\* Last modified Sun Sep 27 17:37:51 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
