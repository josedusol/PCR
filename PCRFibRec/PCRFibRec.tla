---------------------------- MODULE PCRFibRec -------------------------------

(*
   PCR FibRec
   
   ----------------------------------------------------------
     fun idProd, recursion, projectRed
     
     fun idProd(N,p,i) = N
     
     fun recursion(N,p,i) =      \\ N = p[i]
       if   p[i] < 2
       then 1
       else FibRec(p[i]-1) + FibRec(p[i]-2)
     
     fun projectRet(r1,r2) = r2 
     
     lbnd idProd = lambda x. 0 
     ubnd idProd = lambda x. if x < 2 then 0 else 1
     
     PCR FibRec(N):
       par
         p = produce idProd N
         forall p
           c = consume recursion N p
         r = reduce projectRed 0 c
   ----------------------------------------------------------
*)

EXTENDS PCRFibRecTypes, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

idProd(x, p, I, i) == x

projectRed(x, o, c, I, i) == c[i].v 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == IF x < 2 THEN 0 ELSE 1
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

r0(x) == [v |-> 0, r |-> 0]

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

   PCR:  p = produce idProd N
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> idProd(in(I), v_p(I), I, i), r |-> 0]]         
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
         ![I].v_c[i]   = [v |-> 1, r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(v_p(I)[i].v))

\*(*
\*   Consumer recursive call action
\**)
\*C_call1(I) == 
\*  \E i \in iterator(I) :
\*    /\ written(v_p(I), i)
\*    /\ ~ wellDef(I \o <<i>>)
\*    /\ ~ (v_p(I)[i].v < 2)
\*    /\ cm' = [cm EXCEPT 
\*         ![I].v_p[i].r = 1,
\*         ![I \o <<i>>] = initCtx(v_p(I)[i].v - 1) ]      
\*    /\ PrintT("C_call1" \o ToString(I \o <<j>>) 
\*                        \o " : in= " \o ToString(out(I \o <<j>>)'))                                                                                                                                            

\*(*
\*   Consumer recursive call action
\**)
\*C_call2(I) == 
\*  \E i \in iterator(I) :
\*    /\ written(v_p(I), i)
\*    /\ ~ wellDef(I \o <<i>>)
\*    /\ ~ (v_p(I)[i].v < 2)
\*    /\ j = 1
\*    /\ cm' = [cm EXCEPT 
\*         ![I].v_p[i].r = 1,
\*         ![I \o <<i>>] = initCtx(v_p(I)[i].v - 2) ]      
\*    /\ PrintT("C_call2" \o ToString(I \o <<j>>) 
\*                        \o " : in= " \o ToString(out(I \o <<j>>)'))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i, j \in iterator(I) :
    /\ i # j
    /\ written(v_p(I), i)
    /\ written(v_p(I), j)
    /\ ~ wellDef(I \o <<i>>)
    /\ ~ wellDef(I \o <<j>>)
    /\ ~ (v_p(I)[i].v < 2)
    /\ ~ (v_p(I)[j].v < 2)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_p[j].r = @ + 1,
         ![I \o <<i>>] = initCtx(v_p(I)[i].v - 1),
         ![I \o <<j>>] = initCtx(v_p(I)[j].v - 2)  ]    
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(out(I \o <<i>>)'))

(*
   Consumer recursive end action
*)
C_ret(I) == 
  \E i, j \in iterator(I) :
    /\ i # j 
    /\ written(v_p(I), i)
    /\ written(v_p(I), j)
    /\ ~ written(v_c(I), i)
    /\ ~ written(v_c(I), j)
    /\ wellDef(I \o <<i>>)
    /\ wellDef(I \o <<j>>)     
    /\ finished(I \o <<i>>)   
    /\ finished(I \o <<j>>) 
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> out(I \o <<i>>) + out(I \o <<j>>), r |-> 0],
         ![I].v_c[j] = [v |-> out(I \o <<i>>) + out(I \o <<j>>), r |-> 0]   ]  
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

   PCR:  c = reduce projectRed 0 c
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
   PCR FibRec step at index I 
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
\* Last modified Wed Dec 16 15:07:18 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
