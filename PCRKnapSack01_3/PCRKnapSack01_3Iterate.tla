---------------------- MODULE PCRKnapSack01_3Iterate ------------------------

(*
   PCR KnapSack01_3Step
   
   This is a variant of PCRKnapSack01 where we try to implement the Iterate
   PCR construct using an auxiliary PCR with sequential producer and also
   imposing some extra dependencies between consumer and reducer.   
   
   ---------------------------------------------------------------------
     fun init, getLast, apply, consumeLast, ret, solve, update 
     
     lbnd init = lambda x. 0 
     ubnd init = lambda x. 0                 \\ just one instance
        
     PCR KnapSack01_3(X):
       par
         p = produce init X
         forall p
           c = consume KnapSack01_3Iterate X p
         r = reduce getLast [] c
         
     fun apply(X, R, p, i) = if i = 0 
                             then R                               \\ initial value
                             else KnapSack01_3Step(X, p[i-1], i)  \\ apply step on previous value      
     fun pass(X, R, p, i) = p[i]   
     fun retLast(X, R, o, c, i) = c.last
         
     lbnd apply = lambda x. 0 
     ubnd apply = lambda x. Len(x[1].n)     \\ iterate sequentially on number of items to consider
     step apply = lambda i. i + 1   
     
     dep p(i-1) -> p(i)                     \\ producer is sequential
     dep c(i-1) -> c(i)                     \\ consumer should also be sequential
     dep c(i..) -> r(i)                     \\ reducer should wait for consumer future
         
     PCR KnapSack01_3Iterate(X, R):         \\ auxiliary PCR to simulate "iterate" construct
       par
         p = produce apply X R
         forall p
           c = consume pass X R p    
         r = reduce retLast R X R c         \\ we just want the last value of c       

     lbnd id = lambda x. 0 
     ubnd id = lambda x. Len(x[1].C)        \\ solve in paralell for all weights <= C
     step id = lambda i. i + 1
         
     PCR KnapSack01_3Step(X, R, k):
       par
         p = produce id X R k
         forall p
           c = consume solve X R k p
         r = reduce update R X R k c   
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01_3Types, PCRBase, TLC

VARIABLES cm3

KnapSack01_2Step == INSTANCE PCRKnapSack01_3Step WITH 
  InType    <- InType3,
  CtxIdType <- CtxIdType3,
  IndexType <- IndexType3,  
  VarPType  <- VarPType3,
  VarCType  <- VarCType3,
  VarRType  <- VarRType3,  
  cm        <- cm3 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == x[1].n
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

r0(x) == [v |-> x[2], r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
               ste |-> "OFF"]

pre(x) == TRUE

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

pass(x, p, I, i) == p[i].v

retLast(x, o, c, I, i) == c_last(I)

----------------------------------------------------------------------------

\*(*
\*   Producer action
\**)
\*P_1(I) == 
\*  /\ i_p(I) \in iterator(I)  
\*  /\ i_p(I) = 0
\*  /\ ~ KnapSack01_2Step!wellDef(I \o <<i_p(I)>>)
\*  /\ cm' = [cm EXCEPT 
\*       ![I].v_p[i_p(I)] = [v |-> in(I)[2], r |-> 0]] 
\*  /\ im'  = [im  EXCEPT 
\*       ![I] = step(i_p(I)) ]                       
\*\*  /\ PrintT("P_1" \o ToString(I \o <<i_p(I)>>) 
\*\*                  \o " : in= " \o ToString(i_p(I)))
\*            
\*(*
\*   Producer call action
\**)
\*P_2_call(I) == 
\*  /\ i_p(I) \in iterator(I) 
\*  /\ ~ (i_p(I) = 0) 
\*  /\ ~ KnapSack01_2Step!wellDef(I \o <<i_p(I)>>)
\*  /\ cm3' = [cm3 EXCEPT 
\*       ![I \o <<i_p(I)>>] = KnapSack01_2Step!initCtx(<<in(I)[1], v_p(I)[i_p(I)-1].v, i_p(I)>>) ]                  
\*\*  /\ PrintT("P_2_call" \o ToString(I \o <<i_p(I)>>) 
\*\*                       \o " : in= " \o ToString(i_p(I)))
\*
\*(*
\*   Producer ret action
\**)
\*P_2_ret(I) == 
\*  /\ i_p(I) \in iterator(I)
\*  /\ ~ written(v_p(I), i_p(I))
\*  /\ ~ (i_p(I) = 0) 
\*  /\ KnapSack01_2Step!wellDef(I \o <<i_p(I)>>)
\*  /\ KnapSack01_2Step!finished(I \o <<i_p(I)>>)
\*  /\ cm' = [cm EXCEPT 
\*       ![I].v_p[i_p(I)] = [v |-> KnapSack01_2Step!out(I \o <<i_p(I)>>), r |-> 0]]
\*  /\ im'  = [im  EXCEPT 
\*       ![I] = step(i_p(I)) ]     
\*\*  /\ PrintT("P_2_ret" \o ToString(I \o <<i_p(I)>>) 
\*\*                      \o " : in= "  \o ToString(fibRec!in(I \o <<i_p(I)>>))    
\*\*                      \o " : ret= " \o ToString(fibRec!out(I \o <<i_p(I)>>)))
\*
\*(*
\*   Producer action
\**)
\*P(I) == \/ P_1(I)      /\ UNCHANGED cm3
\*        \/ P_2_call(I) /\ UNCHANGED <<cm,im>>
\*        \/ P_2_ret(I)  /\ UNCHANGED cm3                


(*
   Producer action
*)
P_1(I) == 
  \E i \in iterator(I) :
    /\ i > lowerBnd(in(I)) => written(v_p(I), i-1)      \* dep p(i-1) -> p(i)
    /\ i = 0
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> in(I)[2], r |-> 0] ]                    
\*    /\ PrintT("P_1" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))

(*
   Producer call action
*) 
P_2_call(I) == 
  \E i \in iterator(I) :
    /\ i > lowerBnd(in(I)) => written(v_p(I), i-1)      \* dep p(i-1) -> p(i)
    /\ ~ (i = 0)
    /\ ~ KnapSack01_2Step!wellDef(I \o <<i>>)
    /\ cm3' = [cm3 EXCEPT 
         ![I \o <<i>>] = KnapSack01_2Step!initCtx(<<in(I)[1], v_p(I)[i-1].v, i>>) ]   
\*  /\ PrintT("P_2_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(i)) 
            
(*
   Producer ret action
*)
P_2_ret(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ ~ (i = 0) 
    /\ KnapSack01_2Step!wellDef(I \o <<i>>)
    /\ KnapSack01_2Step!finished(I \o <<i>>)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> KnapSack01_2Step!out(I \o <<i>>), r |-> 0]]   
\*  /\ PrintT("P_2_ret" \o ToString(I \o <<i>>) 
\*                      \o " : in= "  \o ToString(KnapSack01_2Step!in(I \o <<i>>))    
\*                      \o " : ret= " \o ToString(KnapSack01_2Step!out(I \o <<i>>)))

(*
   Producer action
   
   PCR:  p = produce apply X R
*)
P(I) == \/ P_1(I)      /\ UNCHANGED cm3
        \/ P_2_call(I) /\ UNCHANGED cm
        \/ P_2_ret(I)  /\ UNCHANGED cm3


(* 
   Consumer action

   PCR:  c = consume pass X R p 
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ i > lowerBnd(in(I)) => written(v_c(I), i-1)     \* dep c(i-1) -> c(i)                    
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> pass(in(I), v_p(I), I, i), r |-> 0]]                                          
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  
  
(* 
   Reducer action

   PCR:  r = reduce retLast R X R c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ \A j \in iterator(I) : j >= i => written(v_c(I), j)     \* dep c(i..) -> r(i)
    /\ pending(I, i)
    /\ LET newOut == retLast(in(I), out(I), v_c(I), I, i)
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
   PCR KnapSack01_3Iterate step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED cm3
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)
        \/ C(I)     /\ UNCHANGED cm3
        \/ R(I)     /\ UNCHANGED cm3
        \/ Quit(I)  /\ UNCHANGED cm3
 
=============================================================================
\* Modification History
\* Last modified Wed Dec 16 15:55:02 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
