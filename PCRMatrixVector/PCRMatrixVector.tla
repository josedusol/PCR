------------------------- MODULE PCRMatrixVector ---------------------------

(*
   PCR MatrixVector
   
   ---------------------------------------------------------------------
     fun init, until, prodStep, update 
          
     fun prodStep(N, A, X, i, y_l, y_i) = y_l + A[i][y_i+1] * X[i]   
          
     fun until(N, A, X, i, y, y_i) = y_i >= N
     
     fun update(N, A, X, o, c, i) = ...
     
     fun r0(N) = EmptyVec
     
     lbnd MatrixVector = lambda x. 0 
     ubnd MatrixVector = lambda x. x[1]
     step MatrixVector = lambda i. i + 1
        
     PCR MatrixVector(N, A, X):
       par
         p = produce init N A X
         forall p
           c = iterate until prodStep p N A X
         r = reduce update r0(N) N A X c  
   ---------------------------------------------------------------------
*)

EXTENDS PCRMatrixVectorTypes, PCRBase, TLC

VARIABLE ym

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

init(x, p, I, i) == 0
 
prodStep(x, I, i, y_l, y_i) == 
  LET A == x[2]
      X == x[3]
      j == y_i + 1
  IN y_l + (A[<<i,j>>] * X[i])

until(x, I, i, y, y_i) == y_i >= x[1]  

update(x, o, c, I, i) == [o EXCEPT ![i] = c[i].v]

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 1
upperBnd(x) == x[1]
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

r0(x) == [v |-> [j \in 1..x[1] |-> 0], 
          r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
               ste |-> "OFF"]   

pre(x) == /\ Cardinality(DOMAIN x[2]) = x[1] * x[1]  \* X2 is a matrix of size X1xX1
          /\ Len(x[3]) = x[1]                        \* X3 is a vector of len X1

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   PCR:  p = produce init N A X                            
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
   Consumer iterator step action
*)
C_step(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ym[I \o <<i>>] # Undef
    /\ ~ until(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ ~ written(v_c(I), i)            
    /\ ym' = [ym EXCEPT 
         ![I \o <<i>>].v[y_i(I \o <<i>>) + 1] = 
            prodStep(in(I), I, i, y_last(I \o <<i>>), y_i(I \o <<i>>)),
         ![I \o <<i>>].i = @ + 1 ]                        
\*    /\ PrintT("C_step" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(y))                

(*
   Consumer iterator end action
*)
C_end(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ym[I \o <<i>>] # Undef
    /\ until(in(I), I, i, y_v(I \o <<i>>), y_i(I \o <<i>>))
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> y_last(I \o <<i>>), r |-> 0] ]           
\*    /\ PrintT("C_end" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                      \o " con v=" \o ToString(y))

(*
   Consumer iterator action
   
   PCR:  c = iterate until prodStep p N A X
*)
C(I) == \/ C_start(I)     
        \/ C_step(I)  /\ UNCHANGED cm
        \/ C_end(I)   /\ UNCHANGED ym
          
(* 
   Reducer action
   
   PCR:  c = reduce [] update c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == update(in(I), out(I), v_c(I), I, i)
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
   PCR MatrixVector step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED ym
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED ym
        \/ C(I)  
        \/ R(I)    /\ UNCHANGED ym
        \/ Quit(I) /\ UNCHANGED ym
 
=============================================================================
\* Modification History
\* Last modified Wed Dec 16 16:05:59 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
