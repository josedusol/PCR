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

EXTENDS Typedef, PCRBase, TLC

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
                      
initCtx(x) == [in  |-> x,
               v_p |-> [n \in IndexType |-> Undef],
               v_c |-> [n \in IndexType |-> Undef],
               ret |-> 0,
               ste |-> "OFF"]  

pre(x) == TRUE

----------------------------------------------------------------------------
                                          
(* 
   Producer action
   
   FXML:  forall i \in Range(0,UpBnd,Step)
            p[i] = idProd N               
   
   PCR:   p = produce idProd N
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> idProd(in(I), v_p(I), i), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))  

(*
   Consumer non-recursive action
*)
C_base(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
\*    /\ ~ read(v_p(I), i)
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
\*    /\ ~ read(v_p(I), i)
\*    /\ ~ (v_p(I)[i].v < 2)
\*\*    /\ ~ wellDef(I \o <<i>>)
\*    /\ map' = [map EXCEPT 
\*         ![I].v_p[i].r = 1,
\*         ![I \o <<i>>] = initCtx(v_p(I)[i].v - 1) ]      
\*\*    /\ PrintT("C_call1" \o ToString(I \o <<j>>) 
\*\*                        \o " : in= " \o ToString(out(I \o <<j>>)'))                                                                                                                                            

\*(*
\*   Consumer recursive call action
\**)
\*C_call2(I) == 
\*  \E i \in iterator(I) :
\*    /\ written(v_p(I), i)
\*    /\ ~ read(v_p(I), i)
\*    /\ ~ (v_p(I)[i].v < 2)
\*\*    /\ j = 1
\*    /\ map' = [map EXCEPT 
\*         ![I].v_p[i].r  = 1,
\*         ![I \o <<i>>]  = initCtx(v_p(I)[i].v - 2) ]      
\*\*    /\ PrintT("C_call2" \o ToString(I \o <<j>>) 
\*\*                        \o " : in= " \o ToString(out(I \o <<j>>)'))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i, j \in iterator(I) :
    /\ i # j
    /\ written(v_p(I), i)
    /\ written(v_p(I), j)
    /\ ~ read(v_p(I), i)
    /\ ~ read(v_p(I), j)
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
     /\ read(v_p(I), i)      
     /\ read(v_p(I), j) 
     /\ ~ written(v_c(I), i)
     /\ ~ written(v_c(I), j)
     /\ finished(I \o <<i>>)   
     /\ finished(I \o <<j>>) 
     /\ cm' = [cm EXCEPT 
          ![I].v_c[i]= [v |-> out(I \o <<i>>) + out(I \o <<j>>), r |-> 0],
          ![I].v_c[j]= [v |-> out(I \o <<i>>) + out(I \o <<j>>), r |-> 0]   ]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(out(I \o <<i>>)))                

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
  \E i \in iterator(I) :
    /\ written(v_c(I), i)    
    /\ ~ read(v_c(I), i)
    /\ LET newRet == projectRed(out(I), v_c(I)[i].v)
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
\* Last modified Thu Oct 29 14:40:52 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
