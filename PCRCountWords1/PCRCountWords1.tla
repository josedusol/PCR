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

lines(x, p, I, i) == x[1][i]

countWordsInLine(x, p, I, i) == 
  LET words == x[2]
      line  == p[i].v
  IN Fold([w \in DOMAIN words |-> 
             IF words[w] \in Range(line) 
             THEN [w2 \in {words[w]} |-> 
                     Cardinality({n \in DOMAIN line : line[n] = w2})]
             ELSE EmptyBag], 
          EmptyBag,
          LAMBDA b1,b2 : b1 (+) b2)
  
joinCounts(x, o, c, I, i) == o (+) c[i].v   

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

r0(x) == [v |-> EmptyBag, r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
               ste |-> "OFF"] 

pre(x) == TRUE

----------------------------------------------------------------------------
            
(* 
   Producer action

   PCR:  p = produce lines T                              
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT
         ![I].v_p[i] = [v |-> lines(in(I), v_p(I), I, i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(* 
   Consumer action
   
   PCR:  c = consume countWordsInLine W
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> countWordsInLine(in(I), v_p(I), I, i), r |-> 0] ]                  
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))    
  
(* 
   Reducer action
   
   PCR:  c = reduce joinCounts {} c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == joinCounts(in(I), out(I), v_c(I), I, i)
           endSte == rDone(I, i) \/ eCnd(newOut)
       IN  cm' = [cm EXCEPT 
             ![I].v_c[i].r = @ + 1,
             ![I].v_r[i]   = [v |-> newOut, r |-> 1],
             ![I].i_r      = i,
             ![I].ste      = IF endSte THEN "END" ELSE @]                                                                            
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
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
\* Last modified Wed Dec 16 15:11:34 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
