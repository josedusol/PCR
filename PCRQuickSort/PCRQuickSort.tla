-------------------------- MODULE PCRQuickSort -----------------------------

(*
   PCR QuickSort 
   
   ---------------------------------------------------------------
     fun iterDivide, divide, isBase, base, conquer
     
     fun iterDivide(X,i) = divide(X)[i]
     
     fun divide(X) = [ partitionLeft(tail(x), X[1]),
                       partitionRight(tail(x), X[1]) ]
     
     fun subproblem(X,p,i) = if   isBase(X, p, i)
                             then base(X, p, i)
                             else QuickSort(X)
   
     fun conquer(X, c, i) = c[1] ++ X[1] ++ c[2]
   
     dep c -> r(i)
   
     PCR QuickSort(X)
       par
         p = produce iterDivide X
         forall p
           c = consume subproblem X p
         r = reduce [] conquer X c
   ---------------------------------------------------------------  
*)

EXTENDS PCRQuickSortTypes, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

\*Position(s, e) == CHOOSE i \in 1..Len(s) : s[i] = e
\*
\*max(a, b) == IF a >= b THEN a ELSE b
\*
\*medianOf(a, b, c) == LET x == max(a, max(b, c))
\*                     IN  CASE  x = a  ->  max(b, c)
\*                           []  x = b  ->  max(a, c)
\*                           []  OTHER  ->  max(a, b)                                                 

partitionLeft(seq, pivot) == 
  LET f[s \in Seq(Elem)] ==
        IF s = << >> 
        THEN << >> 
        ELSE IF Head(s) <= pivot
             THEN <<Head(s)>> \o f[Tail(s)]
             ELSE f[Tail(s)]
  IN f[seq]

partitionRight(seq, pivot) == 
  LET f[s \in Seq(Elem)] ==
        IF s = << >> 
        THEN << >> 
        ELSE IF Head(s) > pivot
             THEN <<Head(s)>> \o f[Tail(s)]
             ELSE f[Tail(s)]
  IN f[seq]   

isBaseCase(x) == Len(x) <= 1

divide(x) == 
  IF isBaseCase(x)
  THEN << x >>
  ELSE LET piv == Head(x)
       IN << partitionLeft(Tail(x), piv), 
             partitionRight(Tail(x), piv) >>               

iterDivide(x, p, i) == divide(x)[i]

base(x, p, i) == p[i].v

isBase(x, p, i) == isBaseCase(p[i].v)

conquer(x, o, c, I, i) == 
  IF isBaseCase(x)
  THEN c[1].v
  ELSE LET piv == Head(x)
       IN  c[1].v \o <<piv>> \o c[2].v

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 1
upperBnd(x) == Len(divide(x))
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
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               ret |-> <<>>,
               ste |-> "OFF"] 

pre(x) == TRUE

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall i \in 1..Len(divide(B))
            p[j] = divide L             
   
   PCR:   p = produce divide L                              
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> iterDivide(in(I), v_p(I), i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer non-recursive action
*)
C_base(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ isBase(in(I), v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> base(in(I), v_p(I), i), r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(v_p(I)[i].v))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ ~ isBase(in(I), v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I \o <<i>>] = initCtx(v_p(I)[i].v) ]              
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer recursive end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)
     /\ read(v_p(I), i)       
     /\ ~ written(v_c(I), i)
     /\ wellDef(I \o <<i>>)
     /\ finished(I \o <<i>>)   
     /\ cm' = [cm EXCEPT 
          ![I].v_c[i] = [v |-> out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(Out(I \o <<i>>)))                

(*
   Consumer action
*)
C(I) == \/ C_base(I)
        \/ C_call(I) 
        \/ C_ret(I)   
          
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ \A j \in iterator(I) : written(v_c(I), j)           \* dep c -> r(i)    
    /\ ~ read(v_c(I), i)
    /\ LET newRet == conquer(in(I), out(I), v_c(I), i)
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
   PCR QuickSort step at index I 
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
\* Last modified Fri Dec 04 17:20:40 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
