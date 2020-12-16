------------------------ MODULE PCRNQueensFirstIT --------------------------

(*
   PCR NQueensFirstIT
   
   ---------------------------------------------------------------------
     fun divide, complete, abs, canAddQueenInRow, 
         canAddQueenInCell, canAddQueens, addQueenInRow, addQueen
        
     fun found(y, i) = if i > 0 then y[i] == y[i-1] else false
     
     fun eureka(r) = \exists c \in r : complete(c)
     
     pre NQueensFirstIT = \forall r \in 1..Len(X) : X[r] == 0
   
     PCR NQueensFirstIT(X : [Nat]) : {[Nat]}  
       par
         p = produce id X
         forall p
           c = iterate found NQueensFirstStep [X]
         r = reduce ret {} c
       
     PCR NQueensFirstITStep(X : {[Nat]}) : {[Nat]}
       par
         p = produce elem X
         forall p
           c = consume extend X p
         r = reduce eureka union {} c    
   ---------------------------------------------------------------------
*)

EXTENDS PCRNQueensFirstITTypes, PCRBase, TLC

VARIABLES ym, cm2

NQueensStep == INSTANCE PCRNQueensFirstITStep WITH 
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

id(x, p, I, i) == x

ret(x, o, c, I, i) == c[i].v

\* complete(x) == \A r \in DOMAIN x : x[r] # 0
\* found(y, i) == y[i] = {} \/ \E c \in y[i] : complete(c)
found(y, i) == IF i > 0 THEN y[i] = y[i-1] ELSE FALSE

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

r0(x) == [v |-> {}, r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
               ste |-> "OFF"] 

pre(x) == \A r \in DOMAIN x : x[r] = 0

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
         ![I].v_p[i] = [v |-> id(in(I), v_p(I), I, i), r |-> 0] ]             
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
                                   THEN { in(I) } 
                                   ELSE Undef],
                          i |-> 0] ]                      
\*    /\ PrintT("C_start" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                        \o " con v=" \o ToString(y'))

(*
   Consumer iterator call action
*)
C_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ym[I \o <<i>>] # Undef
    /\ ~ found(y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ ~ NQueensStep!wellDef(I \o <<i, y_i(I \o <<i>>)>>)
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i, y_i(I \o <<i>>)>>] = NQueensStep!initCtx(y_last(I \o <<i>>)) ]     
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(in(I \o <<i>>)'))                                                                                                                                            


(*
   Consumer iterator return action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)
     /\ ym[I \o <<i>>] # Undef    
     /\ ~ found(y_v(I \o <<i>>), y_i(I \o <<i>>))
     /\ NQueensStep!wellDef(I \o <<i, y_i(I \o <<i>>)>>) 
     /\ NQueensStep!finished(I \o <<i, y_i(I \o <<i>>)>>)   
     /\ ym' = [ym EXCEPT 
          ![I \o <<i>>].v[y_i(I \o <<i>>) + 1] = NQueensStep!out(I \o <<i, y_i(I \o <<i>>)>>),
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
    /\ ~ written(v_c(I), i)
    /\ ym[I \o <<i>>] # Undef  
    /\ found(y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> y_last(I \o <<i>>), r |-> 0] ]               
\*    /\ PrintT("C_end" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                      \o " con v=" \o ToString(y))

(*
   Consumer iterator action
*)
C(I) == \/ C_start(I) /\ UNCHANGED cm2        
        \/ C_call(I)  /\ UNCHANGED <<cm,ym>>
        \/ C_ret(I)   /\ UNCHANGED <<cm,cm2>>
        \/ C_end(I)   /\ UNCHANGED <<cm2,ym>>
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   c = reduce ret {} c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == ret(in(I), out(I), v_c(I), I, i)
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
   PCR NQueensFirstIT step at index I 
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
\* Last modified Tue Dec 15 21:01:06 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
