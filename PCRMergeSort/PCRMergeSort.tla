-------------------------- MODULE PCRMergeSort -----------------------------

(*
   PCR MergeSort 
   
   ---------------------------------------------------------------
     fun iterDivide, divide, isBase, base, conquer, merge
     
     fun iterDivide(L, j) = divide(L)[j]
     
     fun divide(L) = [ L[1..Len(L)/2],
                       L[(Len(L)/2)+1..Len(L)] ]
     
     fun subproblem(L, p, j) = if   isBase(L, p, j)
                               then base(L, p, j)
                               else MergeSort(L, p, j)
   
     fun conquer(a, b) = merge(a,b)
   
     PCR MergeSort(L):
       par
         p = produce iterDivide L
         forall p
           c = consume subproblem L p
         r = reduce conquer [] c
   ---------------------------------------------------------------  
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

divide(x) == LET mid == Len(x) \div 2
             IN  << SubSeq(x, 1, mid),  SubSeq(x, mid+1, Len(x)) >>

iterDivide(x, p, j) == divide(x)[j]

base(x, p, j) == p[j].v

isBase(x, p, j) == Len(p[j].v) <= 1

merge(seq1,seq2) ==
  LET F[s1, s2 \in Seq(Elem)] ==
        IF s1 = << >> 
        THEN s2 
        ELSE IF s2 = << >> 
             THEN s1 
             ELSE CASE Head(s1) <= Head(s2) -> <<Head(s1)>> \o F[Tail(s1), s2]
                    [] Head(s1) > Head(s2)  -> <<Head(s2)>> \o F[s1, Tail(s2)]
  IN F[seq1, seq2] 
 
conquer(old, new) == merge(old, new)

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 1
UpperBnd(x) == Len(divide(x))
Step(j)     == j + 1  

INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step

InitCtx(x) == [in  |-> x,
               i_p |-> LowerBnd(x),
               v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               ret |-> <<>>,
               ste |-> "OFF"] 

Pre(x) == TRUE

Eureka(i) == FALSE

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall j \in 1..Len(divide(B))
            p[j] = divide L             
   
   PCR:   p = produce divide L                              
*)
P(i) == 
  \E j \in Iterator(i) : 
    /\ ~ Written(v_p(i), j)         
    /\ map' = [map EXCEPT  
         ![i].v_p[j] = [v |-> iterDivide(in(i), v_p(i), j), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(i \o <<j>>) \o " : " \o ToString(v_p(i)[j].v'))                  

(*
   Consumer non-recursive action
*)
C_base(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ isBase(in(i), v_p(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = @ + 1,
         ![i].v_c[j]   = [v |-> base(in(i), v_p(i), j), r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(j) \o " : P" \o ToString(j) 
\*                       \o " con v=" \o ToString(v_p(i)[j].v))

(*
   Consumer recursive call action
*)
C_call(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ isBase(in(i), v_p(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r  = 1,
         ![i \o <<j>>]  = InitCtx(v_p(i)[j].v) ]      
\*    /\ PrintT("C_call" \o ToString(i \o <<j>>) 
\*                       \o " : in= " \o ToString(v_p(i)[j].v))                                                                                                                                            

(*
   Consumer recursive end action
*)
C_ret(i) == 
  \E j \in Iterator(i) :
     /\ Read(v_p(i), j)       
     /\ ~ Written(v_c(i), j)
     /\ Finished(i \o <<j>>)   
     /\ map' = [map EXCEPT 
          ![i].v_c[j]= [v |-> Out(i \o <<j>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(i \o <<j>>) 
\*                       \o " : in= "  \o ToString(in(i \o <<j>>))    
\*                       \o " : ret= " \o ToString(Out(i \o <<j>>)))                

(*
   Consumer action
*)
C(i) == \/ C_base(i)
        \/ C_call(i) 
        \/ C_ret(i) 
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_c(i), j)
    /\ ~ Read(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].ret      = conquer(@, v_c(i)[j].v),
         ![i].v_c[j].r = @ + 1,
         ![i].ste      = IF CDone(i, j) \/ Eureka(i) THEN "END" ELSE @]                                                                            
\*    /\ IF State(i)' = "END"
\*       THEN PrintT("R" \o ToString(i \o <<j>>) 
\*                       \o " : in= "  \o ToString(in(i))    
\*                       \o " : ret= " \o ToString(Out(i)')) 
\*       ELSE TRUE              

Next(i) == 
  \/ /\ State(i) = "OFF" 
     /\ Start(i)
  \/ /\ State(i) = "RUN" 
     /\ \/ P(i) 
        \/ C(i) 
        \/ R(i)
        \/ Quit(i)
 
=============================================================================
\* Modification History
\* Last modified Wed Sep 23 19:03:24 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
