------------------------- MODULE PCRCountWords1 ----------------------------

(*
   PCR CountWords1 
   
   ----------------------------------------------------------
     fun lines, countWordsInLine, joinCounts
   
     fun lbnd lines = lambda x. 1 
     fun ubnd lines = lambda x. Len(x)
     fun step lines = lambda x. x + 1
   
     PCR CountWords1(T, W):
       par
         p = produce lines T
         forall l
           c = consume countWordsInLine W p
         r = reduce joinCounts {} c
   ----------------------------------------------------------  
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

InitCtx(input) == [in  |-> input,
                   i_p |-> LowerBnd(input),
                   v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   ret |-> EmptyBag,
                   ste |-> OFF] 

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

lines(x, p, j) == x[1][j]

countWordsInLine(x, p, j) == 
  LET words == x[2]
      line  == p[j].v
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
   Producer action
   
   FXML:  forall j \in Range(1,Len(T),Step)
            p[j] = lines T             
   
   PCR:   p = produce lines T                              
*)
P(i) == 
  \E j \in Iterator(i) : 
    /\ ~ Written(v_p(i), j)         
    /\ map' = [map EXCEPT      \* iterate over lines
         ![i].v_p[j] = [v |-> lines(in(i), v_p(i), j), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(j) \o " : " \o ToString(v_p(i)[j].v'))                  

(* 
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = countWordsInLine W p[j] 

   PCR:   c = consume countWordsInLine W
*)
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = 1, 
         ![i].v_c[j]   = [v |-> countWordsInLine(in(i), v_p(i), j), r |-> 0] ]                  
\*    /\ PrintT("C" \o ToString(j) \o " : P" \o ToString(j) 
\*                  \o " con v=" \o ToString(v_p(i)[j].v))    
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce joinCounts {} c
*)
R(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_c(i), j)
    /\ ~ Read(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].ret      = joinCounts(@, v_c(i)[j].v),
         ![i].v_c[j].r = @ + 1,
         ![i].ste      = IF CDone(i, j) THEN END ELSE @]                                                                            
\*    /\ IF   CDone(i, j)
\*       THEN PrintT("CW1: in T= " \o ToString(In1(i))
\*                                 \o " W= "   \o ToString(In2(i)) 
\*                                 \o " ret= " \o ToString(Out(i)'))
\*       ELSE TRUE             

Next(i) == 
  \/ /\ State(i) = OFF 
     /\ Start(i)
  \/ /\ State(i) = RUN 
     /\ \/ P(i) 
        \/ C(i) 
        \/ R(i)
        \/ Quit(i)
 
=============================================================================
\* Modification History
\* Last modified Sat Sep 12 19:30:34 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
