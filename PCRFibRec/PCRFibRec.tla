---------------------------- MODULE PCRFibRec -------------------------------

(*
   PCR FibRec
   
   ----------------------------------------------------------
     fun idProd, recursion, projectRed
     
     fun idProd(N,p,j) = N
     
     fun recursion(N,p,j) =      \\ N = p[j]
       if   p[j] < 2
       then 1
       else FibRec(p[j]-1, p, j) + FibRec(p[j]-2, p, j)
     
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

idProd(x, p, j) == x

projectRed(r1, r2) == r2 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 0
UpperBnd(x) == IF x < 2 THEN 0 ELSE 1
Step(j)     == j + 1
 
INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step
                      
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
   
   FXML:  forall j \in Range(0,UpBnd,Step)
            p[j] = idProd N               
   
   PCR:   p = produce idProd N
*)
P(i) == 
  \E j \in Iterator(i) :
    /\ ~ Written(v_p(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j] = [v |-> idProd(in(i), v_p(i), j), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(i \o <<j>>) \o " : " \o ToString(v_p(i)[j].v'))  

(*
   Consumer non-recursive action
*)
C_base(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ v_p(i)[j].v < 2
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = @ + 1,
         ![i].v_c[j]   = [v |-> 1, r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(j) \o " : P" \o ToString(j) 
\*                       \o " con v=" \o ToString(v_p(i)[j].v))

\*(*
\*   Consumer recursive call action
\**)
\*C_call1(i) == 
\*  \E j \in Iterator(i) :
\*    /\ Written(v_p(i), j)
\*    /\ ~ Read(v_p(i), j)
\*    /\ ~ (v_p(i)[j].v < 2)
\*\*    /\ j = 0
\*    /\ map' = [map EXCEPT 
\*         ![i].v_p[j].r  = 1,
\*         ![i \o <<j>>]  = InitCtx(v_p(i)[j].v - 1) ]      
\*\*    /\ PrintT("C_call1" \o ToString(i \o <<j>>) 
\*\*                        \o " : in= " \o ToString(Out(i \o <<j>>)'))                                                                                                                                            
\*
\*(*
\*   Consumer recursive call action
\**)
\*C_call2(i) == 
\*  \E j \in Iterator(i) :
\*    /\ Written(v_p(i), j)
\*    /\ ~ Read(v_p(i), j)
\*    /\ ~ (v_p(i)[j].v < 2)
\*\*    /\ j = 1
\*    /\ map' = [map EXCEPT 
\*         ![i].v_p[j].r  = 1,
\*         ![i \o <<j>>]  = InitCtx(v_p(i)[j].v - 2) ]      
\*\*    /\ PrintT("C_call2" \o ToString(i \o <<j>>) 
\*\*                        \o " : in= " \o ToString(Out(i \o <<j>>)'))

(*
   Consumer recursive call action
*)
C_call(i) == 
  \E j1, j2 \in Iterator(i) :
    /\ j1 # j2
    /\ Written(v_p(i), j1)
    /\ Written(v_p(i), j2)
    /\ ~ Read(v_p(i), j1)
    /\ ~ Read(v_p(i), j2)
    /\ ~ (v_p(i)[j1].v < 2)
    /\ ~ (v_p(i)[j2].v < 2)
    /\ map' = [map EXCEPT 
         ![i].v_p[j1].r  = 1,
         ![i].v_p[j2].r  = 1,
         ![i \o <<j1>>]  = InitCtx(v_p(i)[j1].v - 1),
         ![i \o <<j2>>]  = InitCtx(v_p(i)[j2].v - 2)  ]      
\*    /\ PrintT("C_call" \o ToString(i \o <<j1>>) 
\*                       \o " : in= " \o ToString(Out(i \o <<j1>>)'))

(*
   Consumer recursive end action
*)
C_ret(i) == 
  \E j1, j2 \in Iterator(i) :
     /\ j1 # j2 
     /\ Read(v_p(i), j1)      
     /\ Read(v_p(i), j2) 
     /\ ~ Written(v_c(i), j1)
     /\ ~ Written(v_c(i), j2)
     /\ Finished(i \o <<j1>>)   
     /\ Finished(i \o <<j2>>) 
     /\ map' = [map EXCEPT 
          ![i].v_c[j1]= [v |-> Out(i \o <<j1>>) + Out(i \o <<j2>>), r |-> 0],
          ![i].v_c[j2]= [v |-> Out(i \o <<j1>>) + Out(i \o <<j2>>), r |-> 0]   ]  
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

   PCR:   r = reduce projectRed 0 c
*)
R(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_c(i), j)    
    /\ ~ Read(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].ret      = projectRed(@, v_c(i)[j].v),
         ![i].v_c[j].r = @ + 1,
         ![i].ste      = IF CDone(i, j) THEN "END" ELSE @]
\*    /\ IF   CDone(i, j)
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
\* Last modified Thu Sep 24 13:50:23 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
