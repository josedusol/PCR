-------------------------- MODULE PCRKnapSack01 ----------------------------

(*
   PCR KnapSack01
   
   ---------------------------------------------------------------------
     fun init, getLast, nextItem, solve, update  
        
     cnd found(r) = r.item >= Len(r.data.w)
        
     PCR KnapSack01(X):
       par
         p = produce init X
         forall p
           c = iterate found KnapSack01Step p
         r = reduce getLast [] c
         
     PCR KnapSack01Step(Sol):
       par
         p = produce nextItem Sol
         forall p
           c = consume solve Sol p
         r = reduce update Sol c    
   ---------------------------------------------------------------------
*)

EXTENDS Typedef, PCRBase, TLC

VARIABLE y, cm2

KnapSack01Step == INSTANCE PCRKnapSack01Step WITH 
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,  
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  cm        <- cm2 

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

init(x, p, i) == [data |-> x, 
                  item |-> 0,
                  row  |-> [j \in 1..x.C+1 |-> 0]]
 
getLast(r1, r2) == r2.row[Len(r2.row)]

found(r) == r.item >= Len(r.data.w)

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == 0
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
               ret |-> 0,
               ste |-> "OFF"] 

pre(x) == Len(x.w) = Len(x.v)

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall i \in 1..Len(divide(B))
            p[i] = id B             
   
   PCR:   p = produce id B                            
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> init(in(I), v_p(I), i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer action
*)
C_start(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1]
    /\ y'  = v_p(I)[i].v
\*    /\ PrintT("C_start" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                        \o " con v=" \o ToString(y'))

(*
   Consumer non-recursive action
*)
C_end(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ found(y)
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> y, r |-> 0] ]               
\*    /\ PrintT("C_end" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                      \o " con v=" \o ToString(y))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)
    /\ ~ found(y)
    /\ ~ KnapSack01Step!wellDef(I \o <<i>>)
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = KnapSack01Step!initCtx(y) ]
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(y))                                                                                                                                            

(*
   Consumer recursive return action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)
     /\ read(v_p(I), i)       
     /\ ~ found(y)
     /\ KnapSack01Step!wellDef(I \o <<i>>) 
     /\ KnapSack01Step!finished(I \o <<i>>)   
     /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = Undef ]
     /\ y'   = KnapSack01Step!out(I \o <<i>>)
\*     /\ cm' = [cm EXCEPT 
\*          ![I].v_c[i] = [v |-> NQueensStep!out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(Out(I \o <<i>>)))                

(*
   Consumer action
*)
C(I) == \/ C_start(I) /\ UNCHANGED cm2
        \/ C_end(I)   /\ UNCHANGED <<cm2,y>>
        \/ C_call(I)  /\ UNCHANGED <<cm,y>>
        \/ C_ret(I)   /\ UNCHANGED cm
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ ~ read(v_c(I), i)
    /\ LET newRet == getLast(out(I), v_c(I)[i].v)
           endSte == cDone(I, i) \/ eCnd(newRet)
       IN  cm' = [cm EXCEPT 
             ![I].ret      = newRet,
             ![I].v_c[i].r = @ + 1,
             ![I].ste      = IF endSte THEN "END" ELSE @]
\*          /\ PrintT("ret " \o ToString(newRet))      
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE             

(* 
   PCR NQueensFirstIt step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED <<cm2,y>>
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED <<cm2,y>>
        \/ C(I)  
        \/ R(I)    /\ UNCHANGED <<cm2,y>>
        \/ Quit(I) /\ UNCHANGED <<cm2,y>>
 
=============================================================================
\* Modification History
\* Last modified Wed Nov 04 16:38:09 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
