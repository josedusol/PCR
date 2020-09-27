---------------------------- MODULE PCRFibRec -------------------------------

(*
   PCR FibRec
   
   ----------------------------------------------------------
     fun idProd, recursion, projectRed
     
     fun idProd(N,p,i) = N
     
     fun recursion(N,p,i) =      \\ N = p[i]
       if   p[i] < 2
       then 1
       else FibRec(p[i]-1, p, i) + FibRec(p[i]-2, p, i)
     
     fun projectRet(r1,r2) = r2 
     
     lbnd projectProd = lambda x. 0 
     ubnd projectProd = lambda x. if x < 2 then 0 else 1
     
     PCR FibRec(N):
       par
         p = produce idProd N
         forall p
           c = consume recursion N p
         r = reduce projectRed 0 c
   ----------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

idProd(x, p, i) == x

projectRed(r1, r2) == r2 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 0
UpperBnd(x) == IF x < 2 THEN 0 ELSE 1
Step(i)     == i + 1
ECnd(r)     == FALSE
 
INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step,
  ECnd      <- ECnd

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)
                      
InitCtx(x) == [in  |-> x,
               i_p |-> LowerBnd(x),
               v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               ret |-> 0,
               ste |-> "OFF"]  

Pre(x) == TRUE

----------------------------------------------------------------------------
                                          
(* 
   Producer action
   
   FXML:  forall i \in Range(0,UpBnd,Step)
            p[i] = idProd N               
   
   PCR:   p = produce idProd N
*)
P(I) == 
  \E i \in Iterator(I) :
    /\ ~ Written(v_p(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i] = [v |-> idProd(in(I), v_p(I), i), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))  

(*
   Consumer non-recursive action
*)
C_base(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ Written(v_c(I), i)
    /\ v_p(I)[i].v < 2
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> 1, r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(v_p(I)[i].v))

\*(*
\*   Consumer recursive call action
\**)
\*C_call1(I) == 
\*  \E j \in Iterator(I) :
\*    /\ Written(v_p(I), j)
\*    /\ ~ Read(v_p(I), j)
\*    /\ ~ (v_p(I)[j].v < 2)
\*\*    /\ j = 0
\*    /\ map' = [map EXCEPT 
\*         ![I].v_p[j].r  = 1,
\*         ![I \o <<j>>]  = InitCtx(v_p(I)[j].v - 1) ]      
\*\*    /\ PrintT("C_call1" \o ToString(I \o <<j>>) 
\*\*                        \o " : in= " \o ToString(Out(I \o <<j>>)'))                                                                                                                                            
\*
\*(*
\*   Consumer recursive call action
\**)
\*C_call2(I) == 
\*  \E j \in Iterator(I) :
\*    /\ Written(v_p(I), j)
\*    /\ ~ Read(v_p(I), j)
\*    /\ ~ (v_p(I)[j].v < 2)
\*\*    /\ j = 1
\*    /\ map' = [map EXCEPT 
\*         ![I].v_p[j].r  = 1,
\*         ![I \o <<j>>]  = InitCtx(v_p(I)[j].v - 2) ]      
\*\*    /\ PrintT("C_call2" \o ToString(I \o <<j>>) 
\*\*                        \o " : in= " \o ToString(Out(I \o <<j>>)'))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i, j \in Iterator(I) :
    /\ i # j
    /\ Written(v_p(I), i)
    /\ Written(v_p(I), j)
    /\ ~ Read(v_p(I), i)
    /\ ~ Read(v_p(I), j)
    /\ ~ (v_p(I)[i].v < 2)
    /\ ~ (v_p(I)[j].v < 2)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r  = 1,
         ![I].v_p[j].r  = 1,
         ![I \o <<i>>]  = InitCtx(v_p(I)[i].v - 1),
         ![I \o <<j>>]  = InitCtx(v_p(I)[j].v - 2)  ]      
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(Out(I \o <<i>>)'))

(*
   Consumer recursive end action
*)
C_ret(I) == 
  \E i, j \in Iterator(I) :
     /\ i # j 
     /\ Read(v_p(I), i)      
     /\ Read(v_p(I), j) 
     /\ ~ Written(v_c(I), i)
     /\ ~ Written(v_c(I), j)
     /\ Finished(I \o <<i>>)   
     /\ Finished(I \o <<j>>) 
     /\ map' = [map EXCEPT 
          ![I].v_c[i]= [v |-> Out(I \o <<i>>) + Out(I \o <<j>>), r |-> 0],
          ![I].v_c[j]= [v |-> Out(I \o <<i>>) + Out(I \o <<j>>), r |-> 0]   ]  
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

   PCR:   r = reduce projectRed 0 c
*)
R(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_c(I), i)    
    /\ ~ Read(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].ret      = projectRed(@, v_c(I)[i].v),
         ![I].v_c[i].r = @ + 1,
         ![I].ste      = IF CDone(I, i) THEN "END" ELSE @]
\*    /\ IF   CDone(I, i)
\*       THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I))    
\*                       \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE    

(* 
   PCR FibRec step at index I 
*)     
Next(I) == 
  \/ /\ State(I) = "OFF"
     /\ Start(I)
  \/ /\ State(I) = "RUN"
     /\ \/ P(I) 
        \/ C(I) 
        \/ R(I)
        \/ Eureka(I)        
        \/ Quit(I)    

=============================================================================
\* Modification History
\* Last modified Sun Sep 27 16:06:47 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
