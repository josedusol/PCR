------------------------- MODULE PCRCountWords2 ----------------------------

(*
   PCR CountWords2
   
   ----------------------------------------------------------
     fun lines, joinCounts
     
     PCR CountWords2(T, W):
       par
         l = produce lines T
         forall l
           c = consume countInLine l W   \\ call countInLine PCR as a function
         r = reduce joinCounts {} c        
   ----------------------------------------------------------   
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

VARIABLES map2

InitCtx(input) == [in  |-> input,
                   i_p |-> 1,
                   v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   ret |-> EmptyBag,
                   ste |-> OFF] 

----------------------------------------------------------------------------

(* 
   Basic functions                         
*)

lines(x, p, j) == x[1][j]

joinCounts(old, new) == old (+) new  
 
countInLine == INSTANCE PCRCountWordsInLine WITH
  InType    <- InType2,
  LowerBnd  <- LAMBDA x : 1,
  UpperBnd  <- LAMBDA x : Len(x[2]),  
  Step      <- LAMBDA x : x+1,   
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  CtxIdType <- CtxIdType2,
  map       <- map2  

----------------------------------------------------------------------------

(* 
   Producer action

   FXML:  forall i \in 1..Len(T)
            v_p[i] = lines T i             
   
   PCR:   v_p = produce lines T                              
*)
P(i) == 
  /\ \E j \in Iterator(i) :
       /\ ~ Written(v_p(i), j)             
       /\ map' = [map EXCEPT      \* iterate over lines
            ![i].v_p[j] = [v |-> lines(in(i), v_p(i), j), r |-> 0] ]          
\*       /\ PrintT("P" \o ToString(j) \o " : " \o ToString(v_p(i)[j].v'))   

(* 
  Consumer call action 
*)
C_call(i) == 
  \E j \in Iterator(i) :
     /\ Written(v_p(i), j)
     /\ ~ Read(v_p(i), j)
     /\ map'  = [map  EXCEPT ![i].v_p[j].r = 1] 
     /\ map2' = [map2 EXCEPT 
          ![i \o <<j>>]= countInLine!InitCtx(<<v_p(i)[j].v, In2(i)>>)]    
\*     /\ PrintT("C_call " \o ToString(i \o <<j>>) 
\*                         \o " : in= " \o ToString(v_p(i)[j].v))                                                                                                                                            

(* 
  Consumer end action 
*)
C_ret(i) == 
  /\ \E j \in Iterator(i) :
       /\ Read(v_p(i), j)       
       /\ ~ Written(v_c(i), j)
       /\ countInLine!Finished(i \o <<j>>)   
       /\ map' = [map EXCEPT 
            ![i].v_c[j]= [v |-> countInLine!Out(i \o <<j>>), r |-> 0] ]  
\*       /\ PrintT("C_ret" \o ToString(i \o <<j>>) 
\*                         \o " : in= "  \o ToString(countInLine!in(i \o <<j>>))    
\*                         \o " : ret= " \o ToString(countInLine!Out(i \o <<j>>)))                    

(* 
  Consumer action 
*)
C(i) == \/ C_call(i) 
        \/ C_ret(i) /\ UNCHANGED map2    

(* 
   Reducer action
   
   FXML:  forall i \in Dom(v_p)
            r[j+1] = r[j] + count W i 

   PCR:   r = reduce joinCounts {} v_c
*)
R(i) == 
  /\ \E j \in Iterator(i) :
       /\ Written(v_c(i), j)  
       /\ ~ Read(v_c(i), j)
       /\ map' = [map EXCEPT 
            ![i].ret      = joinCounts(@, v_c(i)[j].v),
            ![i].v_c[j].r = @ + 1,
            ![i].ste      = IF CDone(i, j) THEN END ELSE @]                                                                 
\*       /\ IF CDone(i, j)
\*          THEN PrintT("CW: in T= " \o ToString(In1(i))
\*                                   \o " W= "   \o ToString(In2(i)) 
\*                                   \o " ret= " \o ToString(Out(i)'))
\*          ELSE TRUE                

Next(i) == 
  \/ /\ Off(i) 
     /\ Start(i)   
     /\ UNCHANGED map2
  \/ /\ Running(i) 
     /\ \/ P(i)    /\ UNCHANGED map2
        \/ C(i)  
        \/ R(i)    /\ UNCHANGED map2
        \/ Quit(i) /\ UNCHANGED map2  
 
=============================================================================
\* Modification History
\* Last modified Thu Sep 10 01:48:50 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
