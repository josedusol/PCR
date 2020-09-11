----------------------- MODULE PCRCountWordsInLine -------------------------

(*
   PCR CountWordsInLine
   
   ----------------------------------------------------------
     fun elem, count, joinCounts
    
     PCR CountWordsInLine(L, W):
       par
         w = produce elem W
         forall w
           c = consume count L w
         r = reduce joinCounts {} c       
   ----------------------------------------------------------      
*)

EXTENDS PCRBase, Bags

LOCAL INSTANCE TLC

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

elem(x, p, j) == x[2][j]

count(x, p, j) == 
  LET line == x[1]
      word == p[j].v
  IN  IF   word \in Range(line) 
      THEN [w2 \in {word} |-> 
                 Cardinality({n \in DOMAIN line : line[n] = w2})]
      ELSE EmptyBag

joinCounts(old, new) == old (+) new 

----------------------------------------------------------------------------
                                                    
(* 
   Producer action

   FXML: forall j \in 1..Len(T)
           v_p[j] = elem W j             
   
   PCR:  v_p = produce elem W                              
*)
P(i) == 
  \E j \in Iterator(i):
    /\ ~ Written(v_p(i), j)           \* iterate over words
    /\ map' = [map EXCEPT 
         ![i].v_p[j] = [v |-> elem(in(i), v_p(i), j), r |-> 0] ]          
\*    /\ PrintT("P" \o ToString(j) \o " : " \o ToString(v_p(i)[j].v'))   


(* 
   Consumer action
   
   FXML:  forall j \in Dom(v_p)
            v_c[j] = count L j 

   PCR:   v_c = consume count L
*) 
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = @ + 1,
         ![i].v_c[j]   = [v |-> count(in(i), v_p(i), j), r |-> 0]]               
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
\*    /\ IF CDone(i, j)
\*       THEN PrintT("CL FIN: ret = " \o ToString(Out(i)'))
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
\* Last modified Thu Sep 10 01:48:58 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
