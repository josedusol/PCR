-------------------------- MODULE PCRIsPrimeRec ----------------------------

(*
   PCR IsPrimeRec
   
   ----------------------------------------------------------
     fun projectProd, recursion, projectRed
     
     fun projectProd(N,M,p,i) = M
     
     fun recursion(N,M,p,i) =      \\ M = p[i]
       if   p[i] < 2
       then N > 1
       else not (N % p[i] == 0) && IsPrimeRec(N, p[i]-1, p, i)
     
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

projectProd(x, p, i) == x[2]

projectRed(r1, r2) == r2

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

LowerBnd(x) == 0
UpperBnd(x) == 0
Step(i)     == i + 1
 
INSTANCE PCRIterationSpace WITH
  LowerBnd  <- LowerBnd,
  UpperBnd  <- UpperBnd,  
  Step      <- Step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)
                      
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
P(I) == 
  \E i \in Iterator(I) :
    /\ ~ Written(v_p(I), i)
    /\ map' = [map EXCEPT 
         ![I].v_p[i] = [v |-> projectProd(in(I), v_p(I), i), r |-> 0]]         
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
         ![I].v_c[i]   = [v |-> In1(I) > 1, r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(v_p(I)[i].v))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_p(I), i)
    /\ ~ Read(v_p(I), i)
    /\ ~ (v_p(I)[i].v < 2)
    /\ map' = [map EXCEPT 
         ![I].v_p[i].r  = 1,
         ![I \o <<i>>]  = InitCtx(<<In1(I), v_p(I)[i].v - 1>>) ]      
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer recursive ret action
*)
C_ret(I) == 
  \E i \in Iterator(I) :
     /\ Read(v_p(I), i)       
     /\ ~ Written(v_c(I), i)
     /\ Finished(I \o <<i>>)   
     /\ map' = [map EXCEPT 
          ![I].v_c[i]= [v |-> ~ (In1(I) % v_p(I)[i].v = 0) /\ Out(I \o <<i>>), 
                        r |-> 0]]  
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

   PCR:   r = reduce and True c
*)
R(I) == 
  \E i \in Iterator(I) :
    /\ Written(v_c(I), i)    
    /\ ~ Read(v_c(I), i)
    /\ map' = [map EXCEPT 
         ![I].ret      = projectRed(@, v_c(I)[I].v),
         ![I].v_c[I].r = @ + 1,
         ![I].ste      = IF CDone(I, i) THEN "END" ELSE @]
\*    /\ IF   CDone(I, i)
\*       THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I))    
\*                       \o " : ret= " \o ToString(Out(I)')) 
\*       ELSE TRUE    

(* 
   PCR IsPrimeRec step at index I 
*)         
Next(I) == 
  \/ /\ State(I) = "OFF"
     /\ Start(I)
  \/ /\ State(I) = "RUN"
     /\ \/ P(I) 
        \/ C(I) 
        \/ R(I)
        \/ Quit(I)      

=============================================================================
\* Modification History
\* Last modified Sat Sep 26 16:00:17 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
