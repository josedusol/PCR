----------------------- MODULE PCRCountWordsInLine -------------------------

(*
   PCR CountWordsInLine
   
   ----------------------------------------------------------
     fun elem, count, joinCounts
    
     lbnd elem = lambda x. 1 
     ubnd elem = lambda x. Len(x)
     step elem = lambda x. x + 1
    
     PCR CountWordsInLine(L, W):
       par
         p = produce elem W
         forall p
           c = consume count L p
         r = reduce joinCounts {} c       
   ----------------------------------------------------------      
*)

EXTENDS PCRCountWordsInLineTypes, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                        
*)

elem(x, p, i) == x[2][i]

count(x, p, i) == 
  LET line == x[1]
      word == p[i].v
  IN  IF   word \in Range(line) 
      THEN [w2 \in {word} |-> 
                 Cardinality({n \in DOMAIN line : line[n] = w2})]
      ELSE EmptyBag

joinCounts(r1, r2) == r1 (+) r2 

----------------------------------------------------------------------------
   
(* 
   Iteration space                 
*)   
                 
lowerBnd(x) == 1
upperBnd(x) == Len(x[2])
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
               ret |-> EmptyBag,
               ste |-> "OFF"]

pre(x) == TRUE

----------------------------------------------------------------------------                 
                                                    
(* 
   Producer action

   FXML: forall i \in Range(1,Len(W),Step)
           p[i] = elem W             
   
   PCR:  p = produce elem W                              
*)
P(I) == 
  \E i \in iterator(I):
    /\ ~ written(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> elem(in(I), v_p(I), i), r |-> 0] ]          
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))   


(* 
   Consumer action
   
   FXML:  forall i \in Dom(p)
            c[i] = count L p[i] 

   PCR:   c = consume count L
*) 
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> count(in(I), v_p(I), i), r |-> 0]]               
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))       

(* 
   Reducer action
   
   FXML:  ... 

   PCR:   r = reduce joinCounts {} c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)    
    /\ ~ read(v_c(I), i)
    /\ LET newRet == joinCounts(out(I), v_c(I)[i].v)
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
   PCR CountWordsInLine step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
  \/ /\ state(I) = "RUN"
     /\ \/ P(I) 
        \/ C(I) 
        \/ R(I)
        \/ Quit(I)

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 22:02:20 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
