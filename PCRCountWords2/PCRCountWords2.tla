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

EXTENDS PCRCountWords2Types, PCRBase, TLC

VARIABLES cm2

----------------------------------------------------------------------------

(* 
   Basic functions                         
*)

lines(x, p, I, i) == x[1][i]

joinCounts(x, o, c, I, i) == o (+) c[i].v  
 
countWordsInLine == INSTANCE PCRCountWordsInLine WITH
  InType    <- InType2,
  CtxIdType <- CtxIdType2, 
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  cm        <- cm2

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

pre(x) == \A w1 \in DOMAIN x[2] : 
              ~ \E w2 \in DOMAIN x[2] : 
                  x[2][w1] = x[2][w2] 

----------------------------------------------------------------------------

(* 
   Producer action

   FXML:  forall j \in Range(1,Len(T),Step)
            p[i] = lines T             
   
   PCR:   p = produce lines T                              
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)             
    /\ cm' = [cm EXCEPT
         ![I].v_p[i] = [v |-> lines(in(I), v_p(I), I, i), r |-> 0] ]          
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))   

(* 
  Consumer call action 
*)
C_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ countWordsInLine!wellDef(I \o <<i>>)
    /\ cm'  = [cm  EXCEPT 
         ![I].v_p[i].r = @ + 1] 
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = countWordsInLine!initCtx(<<v_p(I)[i].v, in(I)[2]>>)]            
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(* 
  Consumer end action 
*)
C_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ countWordsInLine!wellDef(I \o <<i>>) 
    /\ countWordsInLine!finished(I \o <<i>>)    
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> countWordsInLine!out(I \o <<i>>), r |-> 0] ]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                      \o " : in= "  \o ToString(countWordsInLine!in(I \o <<i>>))    
\*                      \o " : ret= " \o ToString(countWordsInLine!out(I \o <<i>>)))
(* 
  Consumer action 
*)
C(I) == \/ C_call(I)
        \/ C_ret(I)  /\ UNCHANGED cm2    

(* 
   Reducer action
   
   FXML:  ...

   PCR:   c = reduce joinCounts {} c
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
   PCR CountWords2 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)   
     /\ UNCHANGED cm2
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)      /\ UNCHANGED cm2
        \/ C(I)  
        \/ R(I)      /\ UNCHANGED cm2
        \/ Quit(I)   /\ UNCHANGED cm2 
 
=============================================================================
\* Modification History
\* Last modified Tue Dec 15 20:52:29 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
