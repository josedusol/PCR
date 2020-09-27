------------------------- MODULE PCRCountWords1 ----------------------------

(*
   PCR CountWords1 
   
   ----------------------------------------------------------
     fun lines, countWordsInLine, joinCounts
   
     lbnd lines = lambda x. 1 
     ubnd lines = lambda x. Len(x)
     step lines = lambda x. x + 1
   
     PCR CountWords1(T, W):
       par
         p = produce lines T
         forall p
           c = consume countWordsInLine W p
         r = reduce joinCounts {} c
   ----------------------------------------------------------  
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

lines(x, p, i) == x[1][i]

countWordsInLine(x, p, i) == 
  LET words == x[2]
      line  == p[i].v
  IN Fold([w \in DOMAIN words |-> 
             IF words[w] \in Range(line) 
             THEN [w2 \in {words[w]} |-> 
                     Cardinality({n \in DOMAIN line : line[n] = w2})]
             ELSE EmptyBag], 
          EmptyBag,
          LAMBDA b1,b2 : b1 (+) b2)
  
joinCounts(old, new) == old (+) new   

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
   
   FXML:  forall i \in Range(1,Len(T),Step)
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
   Consumer action
   
   FXML:  forall i \in Dom(p)
            c[i] = countWordsInLine W p[i] 

   PCR:   c = consume countWordsInLine W
*)
C(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ Written(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r = 1, 
         ![I].v_c[i]   = [v |-> countWordsInLine(in(I), v_p(I), i), r |-> 0] ]                  
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))    
  
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
\*       THEN PrintT("CW1 R" \o ToString(I \o <<i>>) 
\*                           \o " : in1= " \o ToString(In1(I))    
\*                           \o " : in2= " \o ToString(In2(I))
\*                           \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE

(* 
   PCR CountWords1 step at index I 
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
\* Last modified Sun Sep 27 16:09:20 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
