------------------------- MODULE PCRKnapSack01_1 ---------------------------

(*
   PCR KnapSack01_1
   
   ---------------------------------------------------------------------
     fun init, until, getLast, id, solve, update 
          
     fun until(X, i, y, y_i) = y_i > X.n
        
     PCR KnapSack01_1(X):
       par
         p = produce init X
         forall p
           c = iterate until KnapSack01_1Step X p
         r = reduce getLast 0 X c
         
     PCR KnapSack01_1Step(X, row, k):
       par
         p = produce id X row k
         forall p
           c = consume solve X row k p
         r = reduce update row X row k c   
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01_1Types, PCRBase, TLC

VARIABLES ym, cm2

KnapSack01Step == INSTANCE PCRKnapSack01_1Step WITH 
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

init(x, p, I, i) == [j \in 1..x.C+1 |-> 0]

until(x, I, i, y, y_i) == y_i > x.n  
 
getLast(x, o, c, I, i) == c[i].v[x.C + 1]   

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
ItMap     == [CtxIdType1_1 -> [v : [IndexType1_1 -> VarCType1 \union {Undef}], 
                               i : IndexType1_1] 
                              \union {Undef}]

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

r0(x) == [v |-> 0, r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
               ste |-> "OFF"] 

pre(x) == Len(x.w) = x.n /\ Len(x.v) = x.n

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   PCR:  p = produce init X                          
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> init(in(I), v_p(I), I, i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer iterator start action
*)
C_start(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ym[I \o <<i>>] = Undef
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1]
    /\ ym' = [ym EXCEPT 
         ![I \o <<i>>] = [v |-> [k \in IndexType1_1 |-> 
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
    /\ ym[I \o <<i>>] # Undef
    /\ ~ until(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ ~ KnapSack01Step!wellDef(I \o <<i, y_i(I \o <<i>>)>>)
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i, y_i(I \o <<i>>)>>] = 
            KnapSack01Step!initCtx(<<in(I), y_last(I \o <<i>>), y_i(I \o <<i>>)>>) ]         
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(y))                                                                                                                                            

(*
   Consumer iterator return action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)
     /\ ym[I \o <<i>>] # Undef
     /\ ~ until(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
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
    /\ ym[I \o <<i>>] # Undef
    /\ ~ written(v_c(I), i)
    /\ until(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> y_last(I \o <<i>>), r |-> 0] ]           
\*    /\ PrintT("C_end" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                      \o " con v=" \o ToString(y))

(*
   Consumer iterator action
   
   PCR:  c = iterate until KnapSack01_1Step X p
*)
C(I) == \/ C_start(I) /\ UNCHANGED cm2        
        \/ C_call(I)  /\ UNCHANGED <<cm,ym>>
        \/ C_ret(I)   /\ UNCHANGED <<cm,cm2>>
        \/ C_end(I)   /\ UNCHANGED <<cm2,ym>>
  
(* 
   Reducer action

   PCR:  c = reduce getLast 0 X c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == getLast(in(I), out(I), v_c(I), I, i)
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
   PCR KnapSack01_1 step at index I 
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
\* Last modified Wed Dec 16 16:00:50 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
