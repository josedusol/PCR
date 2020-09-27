------------------------- MODULE PCRCountWords2 ----------------------------

(*
   PCR CountWords2
   
   ----------------------------------------------------------
     fun lines, joinCounts
     
     lbnd lines = lambda x. 1 
     ubnd lines = lambda x. Len(x)
     step lines = lambda x. x + 1
     
     PCR CountWords2(T, W):
       par
         p = produce lines T
         forall p
           c = consume countWordsInLine W p   \\ call countWordsInLine PCR as a function
         r = reduce joinCounts {} c        
   ----------------------------------------------------------   
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

VARIABLES map2

----------------------------------------------------------------------------

(* 
   Basic functions                         
*)

lines(x, p, i) == x[1][i]

joinCounts(r1, r2) == r1 (+) r2  
 
countWordsInLine == INSTANCE PCRCountWordsInLine WITH
  InType    <- InType2,
  CtxIdType <- CtxIdType2, 
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  map       <- map2  

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 1
UpperBnd(x) == Len(x[1])
Step(i)     == i + 1  
ECnd(r)     == FALSE
 
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
               ret |-> EmptyBag,
               ste |-> "OFF"]

Pre(x) == TRUE

----------------------------------------------------------------------------

(* 
   Producer action

   FXML:  forall j \in Range(1,Len(T),Step)
            p[i] = lines T             
   
   PCR:   p = produce lines T                              
*)
P(I) == 
  \E i \in Iterator(I) :
    /\ ~ Written(v_p(I), i)             
    /\ map' = [map EXCEPT
         ![I].v_p[i] = [v |-> lines(in(I), v_p(I), i), r |-> 0] ]          
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))   

(* 
  Consumer call action 
*)
C_call(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ map'  = [map  EXCEPT ![I].v_p[i].r = 1] 
    /\ map2' = [map2 EXCEPT 
         ![I \o <<i>>]= countWordsInLine!InitCtx(<<v_p(I)[i].v, In2(I)>>)]    
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(* 
  Consumer end action 
*)
C_ret(I) == 
  \E i \in Iterator(I) :
    /\ Read(v_p(I), i)       
    /\ ~ Written(v_c(I), i)
    /\ countWordsInLine!Finished(I \o <<i>>)   
    /\ map' = [map EXCEPT 
         ![I].v_c[i]= [v |-> countWordsInLine!Out(I \o <<i>>), r |-> 0] ]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                      \o " : in= "  \o ToString(countWordsInLine!in(I \o <<i>>))    
\*                      \o " : ret= " \o ToString(countWordsInLine!Out(I \o <<i>>)))
(* 
  Consumer action 
*)
C(I) == \/ C_call(I) 
        \/ C_ret(I) /\ UNCHANGED map2    

(* 
   Reducer action
   
   FXML:  ... 

   PCR:   r = reduce joinCounts {} c
*)
R(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_c(I), i)  
    /\ ~ Read(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].ret      = joinCounts(@, v_c(I)[i].v),
         ![I].v_c[i].r = @ + 1,
         ![I].ste      = IF CDone(I, i) THEN "END" ELSE @]
\*    /\ IF   CDone(I, i)
\*       THEN PrintT("CW2 R" \o ToString(I \o <<i>>) 
\*                           \o " : in1= " \o ToString(In1(I))    
\*                           \o " : in2= " \o ToString(In2(I))
\*                           \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE 

(* 
   PCR CountWords2 step at index I 
*)
Next(I) == 
  \/ /\ State(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED map2
  \/ /\ State(I) = "RUN" 
     /\ \/ P(I)      /\ UNCHANGED map2
        \/ C(I)  
        \/ R(I)      /\ UNCHANGED map2
        \/ Eureka(I) /\ UNCHANGED map2
        \/ Quit(I)   /\ UNCHANGED map2  
 
=============================================================================
\* Modification History
\* Last modified Sun Sep 27 16:09:08 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
