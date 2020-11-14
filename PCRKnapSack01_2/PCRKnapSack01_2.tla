------------------------- MODULE PCRKnapSack01_2 ---------------------------

(*
   PCR KnapSack01_2
   
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
           c = consume KnapSack01_2Iterate p
         r = reduce getLast [] c
         
     fun apply(Y, p, i) = if i = 0 
                          then Y                            \\ initial value
                          else KnapSack01_2Step(p[i-1], i)  \\ apply step on previous value      
     fun consumeLast(Y, p, i) = p.last   
     fun ret(r, z) = z
         
     lbnd apply = lambda x. 0 
     ubnd apply = lambda x. Len(x.data.w)    \\ iterate sequentially on number of items to consider
     step apply = lambda i. i + 1   
     
     dep p(i..) -> c(i)                     \\ consumer should wait for producer future
         
     PCR KnapSack01_2Iterate(Y):            \\ auxiliary PCR to simulate "iterate" construct
       par
         p = produceSeq apply Y
         forall p
           c = consume consumeLast Y p      \\ we just want the last value
         r = reduce ret Y c                 

     lbnd id = lambda x. 0 
     ubnd id = lambda x. Len(x[0].C)        \\ solve in paralell for all weights <= C
     step id = lambda i. i + 1
         
     PCR KnapSack01_2Step(Y, k):
       par
         p = produce id Y k
         forall p
           c = consume solve Y k p
         r = reduce update Y c    
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01_2Types, PCRBase, TLC

VARIABLES cm2, cm3, im2

KnapSack01_2Iterate == INSTANCE PCRKnapSack01_2Iterate WITH 
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,  
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  cm        <- cm2,
  cm3       <- cm3, 
  im        <- im2
  
----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

init(x, p, i) == [data |-> x, 
                  row  |-> [j \in 1..x.C+1 |-> 0]]
 
getLast(r, z) == z.row[z.data.C+1]

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

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               ret |-> 0,
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
         ![I].v_p[i] = [v |-> init(in(I), v_p(I), i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ cm'  = [cm  EXCEPT 
         ![I].v_p[i].r = @ + 1] 
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = KnapSack01_2Iterate!initCtx(v_p(I)[i].v) ]
    /\ im2' = [im2 EXCEPT 
         ![I \o <<i>>] = KnapSack01_2Iterate!lowerBnd(v_p(I)[i].v) ]            
\*    /\ PrintT("C_call" \o ToString(I \o <<j>>) 
\*                       \o " : in= " \o ToString(v_p(I)[j].v))                                                                                                                                            

(*
   Consumer end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)       
    /\ ~ written(v_c(I), i)
    /\ KnapSack01_2Iterate!wellDef(I \o <<i>>) 
    /\ KnapSack01_2Iterate!finished(I \o <<i>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> KnapSack01_2Iterate!out(I \o <<i>>), r |-> 0]]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(isPrime!in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(isPrime!Out(I \o <<i>>)))

(*
   Consumer action
*)
C(I) == \/ C_call(I) /\ UNCHANGED cm3
        \/ C_ret(I)  /\ UNCHANGED <<cm2,cm3,im2>>
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ ~ read(v_c(I), i)
    /\ LET newRet == getLast(out(I), v_c(I)[i].v)
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
   PCR KnapSack01_2 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED <<cm2,cm3,im2>>
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED <<cm2,cm3,im2>>
        \/ C(I)  
        \/ R(I)    /\ UNCHANGED <<cm2,cm3,im2>>
        \/ Quit(I) /\ UNCHANGED <<cm2,cm3,im2>>
 
=============================================================================
\* Modification History
\* Last modified Fri Nov 13 22:07:33 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
