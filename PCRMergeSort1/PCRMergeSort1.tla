-------------------------- MODULE PCRMergeSort1 ----------------------------

(*
   PCR MergeSort 
   
   ---------------------------------------------------------------
     fun iterDivide, divide, isBase, base, conquer, merge
     
     fun iterDivide(L,i) = divide(L)[i]
     
     fun divide(L) = [ L[1..Len(L)/2],
                       L[(Len(L)/2)+1..Len(L)] ]
     
     fun subproblem(L,p,i) = if   isBase(L, p, i)
                             then base(L, p, i)
                             else MergeSort(L)
   
     fun merge(l1,l2)
       if  l1 == []
       then l2
       else if l2 == []
           then l1
           else if head l1 <= head l2
                then [head l1] ++ merge(tail s1, s2)  
                else [head l2] ++ merge(s1, tail s2)
   
     fun conquer(r1,r2) = merge(r1,r2)
   
     PCR MergeSort(L)
       par
         p = produce iterDivide L
         forall p
           c = consume subproblem L p
         r = reduce conquer [] c
   ---------------------------------------------------------------  
*)

EXTENDS PCRMergeSort1Types, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

divide(x) == LET mid == Len(x) \div 2
             IN  << SubSeq(x, 1, mid),  SubSeq(x, mid+1, Len(x)) >>

iterDivide(x, p, i) == divide(x)[i]

base(x, p, i) == p[i].v

isBase(x, p, i) == Len(p[i].v) <= 1

merge(seq1, seq2) ==
  LET F[s1, s2 \in Seq(Elem)] ==
        IF s1 = << >> 
        THEN s2 
        ELSE IF s2 = << >> 
             THEN s1 
             ELSE CASE Head(s1) <= Head(s2) -> <<Head(s1)>> \o F[Tail(s1), s2]
                    [] Head(s1) > Head(s2)  -> <<Head(s2)>> \o F[s1, Tail(s2)]
  IN F[seq1, seq2] 
 
conquer(r, z) == merge(r, z)

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
\*    /\ ~ read(v_p(I), i)
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
    /\ ~ read(v_c(I), i)
    /\ LET newRet == conquer(out(I), v_c(I)[i].v)
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
   PCR MergeSort step at index I 
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
\* Last modified Mon Nov 09 02:44:24 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
