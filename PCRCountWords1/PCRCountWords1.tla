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

EXTENDS PCRCountWords1Types, PCRBase, TLC

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

lowerBnd(x) == 1
upperBnd(x) == Len(x[1])
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
   
   FXML:  forall i \in Range(1,Len(T),Step)
            p[i] = lines T             
   
   PCR:   p = produce lines T                              
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT
         ![I].v_p[i] = [v |-> lines(in(I), v_p(I), i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(* 
   Consumer action
   
   FXML:  forall i \in Dom(p)
            c[i] = countWordsInLine W p[i] 

   PCR:   c = consume countWordsInLine W
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> countWordsInLine(in(I), v_p(I), i), r |-> 0] ]                  
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
\*             THEN PrintT("CW1 R" \o ToString(I \o <<i>>) 
\*                                 \o " : in1= " \o ToString(in1(I))    
\*                                 \o " : in2= " \o ToString(in2(I))
\*                                 \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE

(* 
   PCR CountWords1 step at index I 
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
\* Last modified Mon Nov 09 22:03:24 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
