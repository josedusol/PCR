-------------------------- MODULE PCRKnapSack01 ----------------------------

(*
   PCR KnapSack01
   
   ---------------------------------------------------------------------
     fun init, until, getLast, nextItem, solve, update  
        
     fun until(y, i) = i > Len(y[0].data.w)
        
     PCR KnapSack01(X):
       par
         p = produce init X
         forall p
           c = iterate until KnapSack01Step p
         r = reduce getLast [] c
         
     PCR KnapSack01Step(Sol, k):
       par
         p = produce id Sol k
         forall p
           c = consume solve Sol k p
         r = reduce update Sol c   
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01Types, PCRBase, TLC

VARIABLES ym, cm2

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
                  row  |-> [j \in 1..x.C+1 |-> 0]]
 
getLast(r, z) == z.row[Len(z.row)]

until(y, i) == i > Len(y[i].data.w)

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
   Consumer iterator                 
*)

y_i(I)    == ym[I].i
y_v(I)    == ym[I].v
y_last(I) == ym[I].v[ym[I].i]
ItMap     == [CtxIdType -> [v : [IndexType -> VarCType1 \union {Undef}], 
                            i : IndexType] 
                           \union {Undef}]

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
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
   Consumer iterator start action
*)
C_start(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1]
    /\ ym' = [ym EXCEPT 
         ![I \o <<i>>] = [v |-> [k \in IndexType |-> 
                                   IF k = 0 
                                   THEN v_p(I)[i].v 
                                   ELSE Undef],
                          i |-> 0] ]          
\*    /\ PrintT("C_start" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                        \o " con v=" \o ToString(y'))

(*
   Consumer iterator call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)
    /\ ~ until(y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ ~ KnapSack01Step!wellDef(I \o <<i, y_i(I \o <<i>>)>>)
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i, y_i(I \o <<i>>)>>] = 
            KnapSack01Step!initCtx(<<y_last(I \o <<i>>), y_i(I \o <<i>>)>>) ]         
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(y))                                                                                                                                            

(*
   Consumer iterator return action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)
     /\ read(v_p(I), i)
     /\ ~ until(y_v(I \o <<i>>), y_i(I \o <<i>>))
     /\ KnapSack01Step!wellDef(I \o <<i, y_i(I \o <<i>>)>>) 
     /\ KnapSack01Step!finished(I \o <<i, y_i(I \o <<i>>)>>)   
     /\ ym' = [ym EXCEPT 
          ![I \o <<i>>].v[y_i(I \o <<i>>) + 1] = KnapSack01Step!out(I \o <<i, y_i(I \o <<i>>)>>),
          ![I \o <<i>>].i = @ + 1 ]       
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(Out(I \o <<i>>)))                

(*
   Consumer iterator end action
*)
C_end(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ until(y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> y_last(I \o <<i>>), r |-> 0] ]           
\*    /\ PrintT("C_end" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                      \o " con v=" \o ToString(y))

(*
   Consumer action
*)
C(I) == \/ C_start(I) /\ UNCHANGED cm2        
        \/ C_call(I)  /\ UNCHANGED <<cm,ym>>
        \/ C_ret(I)   /\ UNCHANGED <<cm,cm2>>
        \/ C_end(I)   /\ UNCHANGED <<cm2,ym>>
  
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
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE             

(* 
   PCR KnapSack01 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED <<cm2,ym>>
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED <<cm2,ym>>
        \/ C(I)  
        \/ R(I)    /\ UNCHANGED <<cm2,ym>>
        \/ Quit(I) /\ UNCHANGED <<cm2,ym>>
 
=============================================================================
\* Modification History
\* Last modified Mon Nov 09 21:46:29 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
