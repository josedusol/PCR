------------------------- MODULE PCRKnapSack01_3 ---------------------------

(*
   PCR KnapSack01_3
   
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

VARIABLES cm2, cm3

KnapSack01_3Iterate == INSTANCE PCRKnapSack01_3Iterate WITH 
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,  
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  cm        <- cm2,
  cm3       <- cm3
  
----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

init(x, p, I, i) == [j \in 1..x.C+1 |-> 0]    
 
getLast(x, o, c, I, i) == c[i].v[x.C + 1]

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == 0
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

pre(x) == Len(x.w) = x.n /\ Len(x.v) = x.n

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall i \in 1..Len(divide(B))
            p[i] = id B             
   
   PCR:   p = produce id B                            
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> init(in(I), v_p(I), I, i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ KnapSack01_3Iterate!wellDef(I \o <<i>>)
    /\ cm'  = [cm  EXCEPT 
         ![I].v_p[i].r = @ + 1] 
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = KnapSack01_3Iterate!initCtx(<<in(I), v_p(I)[i].v>>) ]           
\*    /\ PrintT("C_call" \o ToString(I \o <<j>>) 
\*                       \o " : in= " \o ToString(v_p(I)[j].v))                                                                                                                                            

(*
   Consumer end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)  
    /\ ~ written(v_c(I), i)
    /\ KnapSack01_3Iterate!wellDef(I \o <<i>>) 
    /\ KnapSack01_3Iterate!finished(I \o <<i>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> KnapSack01_3Iterate!out(I \o <<i>>), r |-> 0]]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(isPrime!in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(isPrime!Out(I \o <<i>>)))

(*
   Consumer action
*)
C(I) == \/ C_call(I) /\ UNCHANGED cm3
        \/ C_ret(I)  /\ UNCHANGED <<cm2,cm3>>          

(* 
   Reducer action
   
   FXML:  ...

   PCR:   c = reduce getLast 0 X c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == getLast(in(I), out(I), v_c(I), I, i)
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
   PCR KnapSack01_3 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED <<cm2,cm3>>
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED <<cm2,cm3>>
        \/ C(I)  
        \/ R(I)    /\ UNCHANGED <<cm2,cm3>>
        \/ Quit(I) /\ UNCHANGED <<cm2,cm3>>
 
=============================================================================
\* Modification History
\* Last modified Wed Dec 16 15:56:56 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
