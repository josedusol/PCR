------------------------- MODULE PCRCountWords1 ----------------------------

(*
   PCR CountWords1 
   
   ----------------------------------------------------------
     fun lines, count, joinCounts
   
     PCR CountWords1(T, W):
       par
         l = produce lines T
         forall l
           c = consume count W l
         r = reduce joinCounts {} c
   ----------------------------------------------------------  
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

InitCtx(input) == [in  |-> input,
                   i_p |-> 1,
                   v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   ret |-> EmptyBag,
                   ste |-> OFF] 

----------------------------------------------------------------------------

(* 
   Basic functions that should be in host language                            
*)

lines(x, p, j) == x[1][j]

count(x, p, j) == 
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
   
   FXML:  forall j \in 1..Len(T)
            v_p[j] = lines T j             
   
   PCR:   v_p = produce lines T                              
*)
P(i) == 
  \E j \in Iterator(i) : 
    /\ ~ Written(v_p(i), j)         
    /\ map' = [map EXCEPT      \* iterate over lines
         ![i].v_p[j] = [v |-> lines(in(i), v_p(i), j), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(j) \o " : " \o ToString(v_p(i)[j].v'))                  

(* 
   Consumer action
   
   FXML:  forall j \in Dom(v_p)
            v_c[j] = count W j 

   PCR:   v_c = consume count W
*)
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = 1, 
         ![i].v_c[j]   = [v |-> count(in(i), v_p(i), j), r |-> 0] ]                  
\*    /\ PrintT("C" \o ToString(j) \o " : P" \o ToString(j) 
\*                  \o " con v=" \o ToString(v_p(i)[j].v))    
  
(* 
   Reducer action
   
   FXML:  forall i \in Dom(v_p)
            r[j+1] = r[j] + count W i 

   PCR:   r = reduce joinCounts {} v_c
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
\*       THEN PrintT("CW: in T= " \o ToString(In1(i))
\*                                \o " W= "   \o ToString(In2(i)) 
\*                                \o " ret= " \o ToString(Out(i)'))
\*       ELSE TRUE             

Next(i) == 
  \/ /\ Off(i) 
     /\ Start(i)
  \/ /\ Running(i) 
     /\ \/ P(i) 
        \/ C(i) 
        \/ R(i)
        \/ Quit(i)
 
=============================================================================
\* Modification History
\* Last modified Wed Sep 09 19:33:45 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
