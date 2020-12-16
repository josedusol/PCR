------------------------- MODULE PCRKnapSack01_4 ---------------------------

(*
   PCR KnapSack01
   
   ---------------------------------------------------------------------
     fun init, until, getLast, nextItem, solve, update  
        
     fun until(X, i, y, y_i) = y_i > X.n
        
     PCR KnapSack01_4(X):
       par
         p = produce init X
         forall p
           par
             c1 = iterate until KnapSack01_4Step X p
             c2 = consume backtrack X c1
         r = reduce retSol [] c1 c2
         
     PCR KnapSack01Step_4(X, S, k):
       par
         p = produce id X S k
         forall p
           c = consume solve X S k p
         r = reduce update S X S c   
   ---------------------------------------------------------------------
*)

EXTENDS PCRKnapSack01_4Types, PCRBase2, TLC

VARIABLES ym, cm2

KnapSack01Step == INSTANCE PCRKnapSack01_4Step WITH 
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

zeroTable(n, m) == [c \in {<<i, j>> : i \in 0..n, j \in 0..m } |-> 0]

init(x, p, I, i) == zeroTable(x.n, x.C) 

backtrack(x, c1, I, i_) == 
  LET table == c1[i_].v
      N == x.n
      C == x.C     
      f[i \in Nat, j \in Nat] ==
         IF   i >= 1
         THEN IF   table[<<i,j>>] # table[<<i-1,j>>]
              THEN f[i - 1, j - x.w[i]] \o <<1>>   
              ELSE f[i - 1, j] \o <<0>>      
         ELSE <<>>    
  IN f[N,C]
 
retSol(x, o, c1, c2, I, i) == [items  |-> c2[i].v, 
                               profit |-> c1[i].v[<<x.n, x.C>>] ]

until(x, I, i, y, y_i) == y_i > x.n

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == 0
step(i)     == i + 1  
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpace2 WITH
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
ItMap     == [CtxIdType1_1 -> [v : [IndexType1_1 -> VarC1Type1 \union {Undef}], 
                               i : IndexType1_1] 
                              \union {Undef}]

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

r0(x) == [v |-> [items |-> <<>>, profit |-> 0], 
          r |-> 0]

initCtx(x) == [in   |-> x,
               v_p  |-> [i \in IndexType |-> Undef],
               v_c1 |-> [i \in IndexType |-> Undef],
               v_c2 |-> [i \in IndexType |-> Undef],
               v_r  |-> [i \in IndexType |-> r0(x)],             
               i_r  |-> lowerBnd(x),
               ste  |-> "OFF"]

pre(x) == Len(x.w) = x.n /\ Len(x.v) = x.n

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
         ![I].v_p[i] = [v |-> init(in(I), v_p(I), I, i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer iterator start action
*)
C1_start(I) == 
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
\*    /\ PrintT("C1_start" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                         \o " con v=" \o ToString(y'))

(*
   Consumer iterator call action
*)
C1_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ym[I \o <<i>>] # Undef
    /\ ~ until(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ ~ KnapSack01Step!wellDef(I \o <<i, y_i(I \o <<i>>)>>)
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i, y_i(I \o <<i>>)>>] = 
            KnapSack01Step!initCtx(<<in(I), y_last(I \o <<i>>), y_i(I \o <<i>>)>>) ]         
\*    /\ PrintT("C1_call" \o ToString(I \o <<i>>) 
\*                        \o " : in= " \o ToString(y))                                                                                                                                            

(*
   Consumer iterator return action
*)
C1_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)
     /\ ym[I \o <<i>>] # Undef
     /\ ~ until(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
     /\ KnapSack01Step!wellDef(I \o <<i, y_i(I \o <<i>>)>>) 
     /\ KnapSack01Step!finished(I \o <<i, y_i(I \o <<i>>)>>)   
     /\ ym' = [ym EXCEPT 
          ![I \o <<i>>].v[y_i(I \o <<i>>) + 1] = KnapSack01Step!out(I \o <<i, y_i(I \o <<i>>)>>),
          ![I \o <<i>>].i = @ + 1 ]       
\*     /\ PrintT("C1_ret" \o ToString(I \o <<i>>) 
\*                        \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                        \o " : ret= " \o ToString(out(I \o <<i>>)))                

(*
   Consumer iterator end action
*)
C1_end(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ym[I \o <<i>>] # Undef
    /\ ~ written(v_c1(I), i)
    /\ until(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ cm' = [cm EXCEPT 
         ![I].v_c1[i] = [v |-> y_last(I \o <<i>>), r |-> 0] ]           
\*    /\ PrintT("C1_end" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(v_c1(I)[i].v'))

(*
   Consumer 1 action
*)
C1(I) == \/ C1_start(I) /\ UNCHANGED cm2        
         \/ C1_call(I)  /\ UNCHANGED <<cm,ym>>
         \/ C1_ret(I)   /\ UNCHANGED <<cm,cm2>>
         \/ C1_end(I)   /\ UNCHANGED <<cm2,ym>>

(*
   Consumer 2 action
*)
C2(I) ==
  \E i \in iterator(I) :
    /\ written(v_c1(I), i)
    /\ ~ written(v_c2(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_c1[i].r = @ + 1, 
         ![I].v_c2[i]   = [v |-> backtrack(in(I), v_c1(I), I, i), r |-> 0] ]                                            
\*    /\ PrintT("C2" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                   \o " con v=" \o ToString(v_c2(I)[i].v'))  
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   c = reduce retSol [] c1 c2
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c2(I), i)
    /\ pending(I, i)
    /\ LET newOut == retSol(in(I), out(I), v_c1(I), v_c2(I), I, i)
           endSte == rDone(I, i) \/ eCnd(newOut)
       IN  cm' = [cm EXCEPT 
             ![I].v_c1[i].r = @ + 1,   \* ???
             ![I].v_c2[i].r = @ + 1,
             ![I].v_r[i]    = [v |-> newOut, r |-> 1],
             ![I].i_r       = i,
             ![I].ste       = IF endSte THEN "END" ELSE @]                                                                            
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE

(* 
   PCR KnapSack01_4 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED <<cm2,ym>>
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED <<cm2,ym>>
        \/ C1(I)  
        \/ C2(I)   /\ UNCHANGED <<cm2,ym>>
        \/ R(I)    /\ UNCHANGED <<cm2,ym>>
        \/ Quit(I) /\ UNCHANGED <<cm2,ym>>
 
=============================================================================
\* Modification History
\* Last modified Tue Dec 15 20:58:47 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
