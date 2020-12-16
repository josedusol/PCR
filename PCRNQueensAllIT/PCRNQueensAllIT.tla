------------------------ MODULE PCRNQueensAllIT --------------------------

(*
   PCR NQueensAllIT
   
   ---------------------------------------------------------------------
    fun divide, complete, abs, canAddQueenInRow, 
        canAddQueenInCell, canAddQueens, addQueenInRow, addQueen
     
     fun divide(X) = 
       cs = []
       for i in 1..Len(X)
         if canAddQueenInRow(X, i) then cs += [addQueenInRow(X, i)]
       return cs
        
     fun found(y, i) = if i > 0 then y[i] == y[i-1] else false
          
     pre NQueensAllIT = \forall r \in 1..Len(X) : X[r] == 0
   
     PCR NQueensAllIT(X : [Nat]) : {[Nat]}
       par
         p = produce id X
         forall p
           c = iterate found NQueensAllITStep [X]
         r = reduce id2 {} c
       
     PCR NQueensAllITStep(X : {[Nat]}) : {[Nat]}
       par
         c = produce elem X
         forall c
           cs = consume extend X c
         r = reduce \union {} X    
   ---------------------------------------------------------------------
*)

EXTENDS PCRNQueensAllITTypes, PCRBase, TLC

VARIABLES ym, cm2

NQueensStep == INSTANCE PCRNQueensAllITStep WITH 
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
 
id2(x, o, c, I, i) == c[i].v

found(x, I, i, y, y_i) == IF y_i > 0 THEN y[y_i] = y[y_i-1] ELSE FALSE

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
   
   PCR:  p = produce id X                            
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
    /\ ~ found(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
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
     /\ ~ found(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
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
    /\ found(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> y_last(I \o <<i>>), r |-> 0] ]               
\*    /\ PrintT("C_end" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                      \o " con v=" \o ToString(y))

(*
   Consumer iterator action
   
   PCR:  c = iterate found NQueensAllITStep [X]
*)
C(I) == \/ C_start(I) /\ UNCHANGED cm2        
        \/ C_call(I)  /\ UNCHANGED <<cm,ym>>
        \/ C_ret(I)   /\ UNCHANGED <<cm,cm2>>
        \/ C_end(I)   /\ UNCHANGED <<cm2,ym>>

(* 
   Reducer action

   PCR:  c = reduce [] conquer c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == id2(in(I), out(I), v_c(I), I, i)
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
   PCR NQueensAllIT step at index I 
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
\* Last modified Wed Dec 16 16:16:49 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
