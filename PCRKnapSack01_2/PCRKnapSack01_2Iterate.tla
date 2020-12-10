---------------------- MODULE PCRKnapSack01_2Iterate ------------------------

(*
   PCR KnapSack01_2Step
   
   This is a variant of PCRKnapSack01 where we try to implement the Iterate
   PCR construct using an auxiliary PCR with sequential producer and also
   imposing some extra dependencies between consumer and reducer.   
   
   ---------------------------------------------------------------------
     fun init, getLast, apply, consumeLast, ret, solve, update 
     
     lbnd init = lambda x. 0 
     ubnd init = lambda x. 0                 \\ just one instance
        
     PCR KnapSack01_2(X):
       par
         p = produce init X
         forall p
           c = consume KnapSack01_2Iterate X p
         r = reduce getLast [] c
         
     fun apply(X, R, p, i) = if i = 0 
                             then R                               \\ initial value
                             else KnapSack01_2Step(X, p[i-1], i)  \\ apply step on previous value      
     fun consumeLast(X, R, p, i) = p.last   
     fun ret(X, R, o, c, i) = c[i]
         
     lbnd apply = lambda x. 0 
     ubnd apply = lambda x. Len(x[1].n)     \\ iterate sequentially on number of items to consider
     step apply = lambda i. i + 1   
     
     dep p(i..) -> c(i)                     \\ consumer should wait for producer future
         
     PCR KnapSack01_2Iterate(X, R):         \\ auxiliary PCR to simulate "iterate" construct
       par
         p = produceSeq apply X R
         forall p
           c = consume consumeLast X R p    \\ we just want the last value
         r = reduce ret X R c                 

     lbnd id = lambda x. 0 
     ubnd id = lambda x. Len(x[1].C)        \\ solve in paralell for all weights <= C
     step id = lambda i. i + 1
         
     PCR KnapSack01_2Step(X, R, k):
       par
         p = produce id X R k
         forall p
           c = consume solve X R k p
         r = reduce update X R k c   
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01_2Types, PCRBase, TLC

VARIABLES cm3, im

KnapSack01_2Step == INSTANCE PCRKnapSack01_2Step WITH 
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
               ret |-> x[2],
               ste |-> "OFF"] 

pre(x) == TRUE

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

consumeLast(x, p, I, i) == p_last(I)     
                       
ret(x, o, c, I, i) == c[i].v

----------------------------------------------------------------------------

(*
   Producer action
*)
P_1(I) == 
  /\ i_p(I) \in iterator(I)  
  /\ i_p(I) = 0
  /\ ~ KnapSack01_2Step!wellDef(I \o <<i_p(I)>>)
  /\ cm' = [cm EXCEPT 
       ![I].v_p[i_p(I)] = [v |-> in(I)[2], r |-> 0]] 
  /\ im'  = [im  EXCEPT 
       ![I] = step(i_p(I)) ]                       
\*  /\ PrintT("P_1" \o ToString(I \o <<i_p(I)>>) 
\*                  \o " : in= " \o ToString(i_p(I)))
            
(*
   Producer call action
*)
P_2_call(I) == 
  /\ i_p(I) \in iterator(I) 
  /\ ~ (i_p(I) = 0) 
  /\ ~ KnapSack01_2Step!wellDef(I \o <<i_p(I)>>)
  /\ cm3' = [cm3 EXCEPT 
       ![I \o <<i_p(I)>>] = KnapSack01_2Step!initCtx(<<in(I)[1], v_p(I)[i_p(I)-1].v, i_p(I)>>) ]                  
\*  /\ PrintT("P_2_call" \o ToString(I \o <<i_p(I)>>) 
\*                       \o " : in= " \o ToString(i_p(I)))

(*
   Producer ret action
*)
P_2_ret(I) == 
  /\ i_p(I) \in iterator(I)
  /\ ~ written(v_p(I), i_p(I))
  /\ ~ (i_p(I) = 0) 
  /\ KnapSack01_2Step!wellDef(I \o <<i_p(I)>>)
  /\ KnapSack01_2Step!finished(I \o <<i_p(I)>>)
  /\ cm' = [cm EXCEPT 
       ![I].v_p[i_p(I)] = [v |-> KnapSack01_2Step!out(I \o <<i_p(I)>>), r |-> 0]]
  /\ im'  = [im  EXCEPT 
       ![I] = step(i_p(I)) ]     
\*  /\ PrintT("P_2_ret" \o ToString(I \o <<i_p(I)>>) 
\*                      \o " : in= "  \o ToString(fibRec!in(I \o <<i_p(I)>>))    
\*                      \o " : ret= " \o ToString(fibRec!out(I \o <<i_p(I)>>)))

(*
   Producer action
*)
P(I) == \/ P_1(I)      /\ UNCHANGED cm3
        \/ P_2_call(I) /\ UNCHANGED <<cm,im>>
        \/ P_2_ret(I)  /\ UNCHANGED cm3                

(* 
   Consumer action
   
   FXML:  forall i \in Dom(p)
            cs[i] = extend X c[i]

   PCR:   cs = consume extend B c
*)
C(I) == 
  \E i \in iterator(I) :                  
    /\ \A j \in iterator(I) : j >= i => written(v_p(I), j)    \* dep p(i..) -> c(i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> consumeLast(in(I), v_p(I), I, i), r |-> 0]]                                          
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)   
    /\ ~ read(v_c(I), i)
    /\ LET newRet == ret(in(I), out(I), v_c(I), I, i)
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
   PCR KnapSack01_2Iterate step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED <<cm3,im>>
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)
        \/ C(I)     /\ UNCHANGED <<cm3,im>>
        \/ R(I)     /\ UNCHANGED <<cm3,im>>
        \/ Quit(I)  /\ UNCHANGED <<cm3,im>>
 
=============================================================================
\* Modification History
\* Last modified Wed Nov 25 14:45:16 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
