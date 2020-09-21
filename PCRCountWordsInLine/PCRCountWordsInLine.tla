----------------------- MODULE PCRCountWordsInLine -------------------------

(*
   PCR CountWordsInLine
   
   ----------------------------------------------------------
     fun elem, count, joinCounts
    
     fun lbnd elem = lambda x. 1 
     fun ubnd elem = lambda x. Len(x)
     fun step elem = lambda x. x + 1
    
     PCR CountWordsInLine(L, W):
       par
         p = produce elem W
         forall p
           c = consume count L p
         r = reduce joinCounts {} c       
   ----------------------------------------------------------      
*)

EXTENDS PCRBase, Bags

LOCAL INSTANCE TLC

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
   Iteration space                 
*)   
                 
LowerBnd(x) == 1
UpperBnd(x) == Len(x[2])
Step(j)     == j + 1  

INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step

InitCtx(x) == [in  |-> x,
               i_p |-> LowerBnd(x),
               v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               ret |-> EmptyBag,
               ste |-> "OFF"]

----------------------------------------------------------------------------                 
                                                    
(* 
   Producer action

   FXML: forall j \in Range(1,Len(W),Step)
           p[j] = elem W             
   
   PCR:  p = produce elem W                              
*)
P(i) == 
  \E j \in Iterator(i):
    /\ ~ Written(v_p(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j] = [v |-> elem(in(i), v_p(i), j), r |-> 0] ]          
\*    /\ PrintT("P" \o ToString(i \o <<j>>) \o " : " \o ToString(v_p(i)[j].v'))   


(* 
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = count L p[j] 

   PCR:   c = consume count L
*) 
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = @ + 1,
         ![i].v_c[j]   = [v |-> count(in(i), v_p(i), j), r |-> 0]]               
\*    /\ PrintT("C" \o ToString(i \o <<j>>) \o " : P" \o ToString(j) 
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
         ![i].ste      = IF CDone(i, j) THEN "END" ELSE @]
\*    /\ IF   CDone(i, j)
\*       THEN PrintT("R" \o ToString(i \o <<j>>) 
\*                       \o " : in= "  \o ToString(in(i))    
\*                       \o " : ret= " \o ToString(Out(i)')) 
\*       ELSE TRUE 

Next(i) == 
  \/ /\ State(i) = "OFF" 
     /\ Start(i)
  \/ /\ State(i) = "RUN"
     /\ \/ P(i) 
        \/ C(i) 
        \/ R(i)
        \/ Quit(i)

=============================================================================
\* Modification History
\* Last modified Sun Sep 20 22:38:08 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
