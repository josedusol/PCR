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

EXTENDS Typedef, PCRBase, TLC

VARIABLES cm2

----------------------------------------------------------------------------

(* 
   Basic functions                         
*)

lines(x, p, i) == x[1][i]

joinCounts(r1, r2) == r1 (+) r2  
 
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

initCtx(x) == [in  |-> x,
               v_p |-> [n \in IndexType |-> Undef],
               v_c |-> [n \in IndexType |-> Undef],
               ret |-> EmptyBag,
               ste |-> "OFF"]

pre(x) == TRUE

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
         ![I].v_p[i] = [v |-> lines(in(I), v_p(I), i), r |-> 0] ]          
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))   

(* 
  Consumer call action 
*)
C_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ cm'  = [cm  EXCEPT 
         ![I].v_p[i].r = @ + 1] 
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = countWordsInLine!initCtx(<<v_p(I)[i].v, in2(I)>>)]            
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(* 
  Consumer end action 
*)
C_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)       
    /\ ~ written(v_c(I), i)
    /\ countWordsInLine!finished(I \o <<i>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> countWordsInLine!out(I \o <<i>>), r |-> 0] ]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                      \o " : in= "  \o ToString(countWordsInLine!in(I \o <<i>>))    
\*                      \o " : ret= " \o ToString(countWordsInLine!Out(I \o <<i>>)))
(* 
  Consumer action 
*)
C(I) == \/ C_call(I)
        \/ C_ret(I)  /\ UNCHANGED cm2    

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
\*             THEN PrintT("CW2 R" \o ToString(I \o <<i>>) 
\*                                 \o " : in1= " \o ToString(in1(I))    
\*                                 \o " : in2= " \o ToString(in2(I))
\*                                 \o " : ret= " \o ToString(out(I)')) 
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
\* Last modified Wed Oct 28 23:24:13 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
