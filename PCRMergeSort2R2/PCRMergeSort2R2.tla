-------------------------- MODULE PCRMergeSort2R2 --------------------------

(*
   PCR MergeSort2R2 
   
   ---------------------------------------------------------------
     fun iterDivide, divide, isBase, base, ret
     
     fun iterDivide(X,p,i) = divide(X)[i]
     
     fun divide(X) = [ L[1..Len(L)/2],
                       L[(Len(L)/2)+1..Len(L)] ]
     
     fun subproblem(X,p,i) = if   isBase(X, p, i)
                             then base(X, p, i)
                             else MergeSort(X)
                             
     fun ret(X,o,c2,i) = c2[i]                        
   
     dep c1 -> c2(i)
   
     PCR MergeSort3(X)
       par
         p = produce iterDivide X
         forall p
           par
             c1 = consume subproblem X p
             c2 = consume merge c1[1] c1[2]     \\ call merge PCR as a function
         r = reduce ret [] c2           
   ---------------------------------------------------------------  
*)

EXTENDS PCRMergeSort2R2Types, PCRBase2R, TLC

VARIABLE cm2

merge == INSTANCE PCRMerge WITH 
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

divide(x) == LET mid == Len(x) \div 2
             IN  << SubSeq(x, 1, mid),  SubSeq(x, mid+1, Len(x)) >>

iterDivide(x, p, i) == divide(x)[i]

base(x, p, i) == p[i].v

isBase(x, p, i) == Len(p[i].v) <= 1

ret(x, o, c1, c2, I, i) == c2[i].v

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 1
upperBnd(x) == Len(divide(x))
step(i)     == i + 1  
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpace2R WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

r0 == [v |-> <<>>, r |-> 0]

initCtx(x) == [in   |-> x,
               v_p  |-> [i \in IndexType |-> Undef],
               v_c1 |-> [i \in IndexType |-> Undef],
               v_c2 |-> [i \in IndexType |-> Undef],
               v_r  |-> [i \in IndexType |-> r0],             
               i_r  |-> lowerBnd(x),
               ste  |-> "OFF"] 

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
   Consumer 1 non-recursive action
*)
C1_base(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c1(I), i)
    /\ isBase(in(I), v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c1[i]  = [v |-> base(in(I), v_p(I), i), r |-> 0] ]               
\*    /\ PrintT("C1_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                        \o " con v=" \o ToString(v_p(I)[i].v))

(*
   Consumer 1 recursive call action
*)
C1_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ ~ isBase(in(I), v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I \o <<i>>] = initCtx(v_p(I)[i].v) ]              
\*    /\ PrintT("C1_call" \o ToString(I \o <<i>>) 
\*                        \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer 1 recursive end action
*)
C1_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)       
    /\ ~ written(v_c1(I), i)
    /\ wellDef(I \o <<i>>)
    /\ finished(I \o <<i>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c1[i] = [v |-> out(I \o <<i>>), r |-> 0]]  
\*    /\ PrintT("C1_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(out(I \o <<i>>)))                

(*
   Consumer 1 action
*)
C1(I) == \/ C1_base(I)
         \/ C1_call(I) 
         \/ C1_ret(I)

(*
   Consumer 2 call action
*)
C2_call(I) == 
  \E i \in iterator(I):
    /\ written(v_c1(I), i)
    /\ ~ merge!wellDef(I \o <<i>>) 
    /\ \A j \in iterator(I) : written(v_c1(I), j)          \* dep c1 -> c2(i)
    /\ cm'  = [cm  EXCEPT 
         ![I].v_c1[i].r = @ + 1] 
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = merge!initCtx(<<v_c1(I)[1].v, v_c1(I)[2].v>>) ]   
\*    /\ PrintT("C2_call" \o ToString(I \o <<j>>) 
\*                        \o " : in= " \o ToString(v_p(I)[j].v))                                                                                                                                            

(*
   Consumer 2 end action
*)
C2_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_c1(I), i)
    /\ read(v_c1(I), i)       
    /\ ~ written(v_c2(I), i)    
    /\ merge!wellDef(I \o <<i>>) 
    /\ merge!finished(I \o <<i>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c2[i] = [v |-> merge!out(I \o <<i>>), r |-> 0]]  
\*    /\ PrintT("C2_ret" \o ToString(I \o <<i>>) 
\*                        \o " : in= "  \o ToString(merge!in(I \o <<i>>))    
\*                        \o " : ret= " \o ToString(merge!Out(I \o <<i>>)))

(*
   Consumer 2 action
*)
C2(I) == \/ C2_call(I)
         \/ C2_ret(I)  /\ UNCHANGED cm2  

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c2(I), i)
    /\ pending(I, i)
    /\ LET newOut == ret(in(I), out(I), v_c1(I), v_c2(I), I, i)
           endSte == rDone(I, i) \/ eCnd(newOut)
       IN  cm' = [cm EXCEPT 
             ![I].v_c2[i].r = @ + 1,
             ![I].v_r[i]    = [v |-> newOut, r |-> 1],
             ![I].i_r       = i,
             ![I].ste       = IF endSte THEN "END" ELSE @]                                                                            
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in  = " \o ToString(in(I))    
\*                             \o " : out = " \o ToString(out(I)')) 
\*             ELSE TRUE    

(* 
   PCR MergeSort2 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED cm2
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED cm2
        \/ C1(I)   /\ UNCHANGED cm2
        \/ C2(I)   
        \/ R(I)    /\ UNCHANGED cm2
        \/ Quit(I) /\ UNCHANGED cm2
 
=============================================================================
\* Modification History
\* Last modified Sun Nov 22 23:03:23 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
