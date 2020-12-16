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
         r = reduce projectRed true c
   ----------------------------------------------------------
*)

EXTENDS PCRIsPrimeRecTypes, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

projectProd(x, p, I, i) == x[2]

projectRed(x, o, c, I, i) == c[i].v

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == 0
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

r0(x) == [v |-> TRUE, r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
               ste |-> "OFF"]  

pre(x) == x[2] = Sqrt(x[1])

----------------------------------------------------------------------------
                                          
(* 
   Producer action
   
   FXML:  forall j \in 0..N
            p[j] = divisors N               
   
   PCR:   p = produce divisors N
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> projectProd(in(I), v_p(I), I, i), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))  

(*
   Consumer non-recursive action
*)
C_base(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ v_p(I)[i].v < 2
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> in1(I) > 1, r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(v_p(I)[i].v))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ wellDef(I \o <<i>>)
    /\ ~ (v_p(I)[i].v < 2)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r  = @ + 1,
         ![I \o <<i>>]  = initCtx(<<in1(I), v_p(I)[i].v - 1>>) ]      
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer recursive ret action
*)
C_ret(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ wellDef(I \o <<i>>)
    /\ finished(I \o <<i>>)   
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i]= [v |-> ~ (in1(I) % v_p(I)[i].v = 0) /\ out(I \o <<i>>), 
                       r |-> 0]]  
\*    /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                      \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                      \o " : ret= " \o ToString(out(I \o <<i>>)))                

(*
   Consumer action
*)
C(I) == \/ C_base(I)
        \/ C_call(I) 
        \/ C_ret(I)   

(* 
   Reducer action
   
   FXML:  ...

   PCR:   c = reduce and True c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == projectRed(in(I), out(I), v_c(I), I, i)
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
   PCR IsPrimeRec step at index I 
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
\* Last modified Tue Dec 15 20:56:15 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
