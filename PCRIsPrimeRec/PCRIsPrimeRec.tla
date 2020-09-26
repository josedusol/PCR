-------------------------- MODULE PCRIsPrimeRec ----------------------------

(*
   PCR IsPrimeRec
   
   ----------------------------------------------------------
     fun projectProd, recursion, projectRed
     
     fun projectProd(N,M,p,j) = M
     
     fun recursion(N,M,p,j) =      \\ M = p[j]
       if   p[j] < 2
       then N > 1
       else not (N % p[j] == 0) && IsPrimeRec(N, p[j]-1, p, j)
     
     fun projectRet(r1,r2) = r2 
     
     lbnd projectProd = lambda x. 0 
     ubnd projectProd = lambda x. 0
   
     pre IsPrimeRec = M == Sqrt(N)
     
     PCR IsPrimeRec(N,M):
       par
         p = produce projectProd N M
         forall p
           c = consume recursion N M p
         r = reduce projectRed True c
   ----------------------------------------------------------
*)

EXTENDS Typedef, PCRBase

LOCAL INSTANCE TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

projectProd(x, p, j) == x[2]

projectRed(r1, r2) == r2

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 0
UpperBnd(x) == 0
Step(j)     == j + 1
 
INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step
                      
InitCtx(x) == [in  |-> x,
               i_p |-> LowerBnd(x),
               v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
               ret |-> TRUE,
               ste |-> "OFF"]  

Pre(x) == x[2] = Sqrt(x[1])

----------------------------------------------------------------------------
                                          
(* 
   Producer action
   
   FXML:  forall j \in 0..N
            p[j] = divisors N               
   
   PCR:   p = produce divisors N
*)
P(i) == 
  \E j \in Iterator(i) :
    /\ ~ Written(v_p(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j] = [v |-> projectProd(in(i), v_p(i), j), r |-> 0]]         
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
         ![i].v_c[j]   = [v |-> In1(i) > 1, r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(j) \o " : P" \o ToString(j) 
\*                       \o " con v=" \o ToString(v_p(i)[j].v))

(*
   Consumer recursive call action
*)
C_call(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ (v_p(i)[j].v < 2)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r  = 1,
         ![i \o <<j>>]  = InitCtx(<<In1(i), v_p(i)[j].v - 1>>) ]      
\*    /\ PrintT("C_call" \o ToString(i \o <<j>>) 
\*                       \o " : in= " \o ToString(v_p(i)[j].v))                                                                                                                                            

(*
   Consumer recursive ret action
*)
C_ret(i) == 
  \E j \in Iterator(i) :
     /\ Read(v_p(i), j)       
     /\ ~ Written(v_c(i), j)
     /\ Finished(i \o <<j>>)   
     /\ map' = [map EXCEPT 
          ![i].v_c[j]= [v |-> ~ (In1(i) % v_p(i)[j].v = 0) /\ Out(i \o <<j>>), 
                        r |-> 0]]  
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

   PCR:   r = reduce and True c
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
\* Last modified Thu Sep 24 13:33:27 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
