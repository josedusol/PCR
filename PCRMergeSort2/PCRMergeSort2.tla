-------------------------- MODULE PCRMergeSort2 ----------------------------

(*
   PCR MergeSort2 
   
   ---------------------------------------------------------------
     fun iterDivide, divide, isBase, base
     
     fun iterDivide(X,i) = divide(X)[i]
     
     fun divide(X) = [ X[1..Len(X)/2],
                       X[(Len(X)/2)+1..Len(X)] ]
     
     fun subproblem(X,p,i) = if   isBase(X, p, i)
                             then base(X, p, i)
                             else MergeSort2(X)
   
     PCR MergeSort2(X)
       par
         p = produce iterDivide X
         forall p
           c = consume subproblem X p
         r = reduce [] merge c           \\ call merge PCR as a function
   ---------------------------------------------------------------  
*)

EXTENDS PCRMergeSort2Types, PCRBase, TLC

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

iterDivide(x, p, I, i) == divide(x)[i]

base(x, p, I, i) == p[i].v

isBase(x, p, I, i) == Len(p[i].v) <= 1

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

r0(x) == [v |-> <<>>, r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
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
         ![I].v_p[i] = [v |-> iterDivide(in(I), v_p(I), I, i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer non-recursive action
*)
C_base(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> base(in(I), v_p(I), I, i), r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(v_p(I)[i].v))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ wellDef(I \o <<i,2>>)
    /\ ~ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r   = @ + 1,
         ![I \o <<i,2>>] = initCtx(v_p(I)[i].v) ]              
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer recursive end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)  
    /\ ~ written(v_c(I), i)
    /\ wellDef(I \o <<i,2>>)
    /\ finished(I \o <<i,2>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> out(I \o <<i,2>>), r |-> 0]]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                      \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                      \o " : ret= " \o ToString(Out(I \o <<i>>)))                

(*
   Consumer action
*)
C(I) == \/ C_base(I)
        \/ C_call(I) 
        \/ C_ret(I)

(* 
   Reducer call action
*)
R_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)    
    /\ ~ merge!wellDef(I \o <<i,3>>)
    /\ ~ \E j \in iterator(I) : 
           /\ j # i 
           /\ merge!wellDef(I \o <<j,3>>)
           /\ pending(I, j)       
    /\ cm'  = [cm  EXCEPT 
         ![I].v_c[i].r = @ + 1] 
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i,3>>] = merge!initCtx(<<out(I), v_c(I)[i].v>>) ] 
\*    /\ PrintT("R_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(merge!in(I \o <<i>>)'))  
  
(* 
   Reducer ret action
*)
R_ret(I) == 
  \E i \in iterator(I) :                         
    /\ written(v_c(I), i)        
    /\ merge!wellDef(I \o <<i,3>>)
    /\ merge!finished(I \o <<i,3>>) 
    /\ pending(I, i)
    /\ LET newOut == merge!out(I \o <<i,3>>)
           endSte == rDone(I, i) \/ eCnd(newOut)
       IN  cm' = [cm EXCEPT 
             ![I].v_r[i]   = [v |-> newOut, r |-> 1],
             ![I].i_r      = i,
             ![I].ste      = IF endSte THEN "END" ELSE @]                                                                             
\*          /\ IF endSte
\*             THEN PrintT("R_ret" \o ToString(I \o <<i>>) 
\*                                 \o " : in= "  \o ToString(in(I))    
\*                                 \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE                

(*
   Reducer action
*)
R(I) == \/ R_call(I)
        \/ R_ret(I)  /\ UNCHANGED cm2 

(* 
   PCR MergeSort2 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED cm2
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED cm2
        \/ C(I)    /\ UNCHANGED cm2
        \/ R(I)  
        \/ Quit(I) /\ UNCHANGED cm2
 
=============================================================================
\* Modification History
\* Last modified Tue Dec 15 20:59:51 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
