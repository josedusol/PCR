-------------------------- MODULE PCRFirstEven -----------------------------

(*
   PCR FirstEven
   
   ----------------------------------------------------------
     fun id, checkEven, reducer
     
     lbnd projectProd = lambda x. 0 
     ubnd projectProd = lambda x. x
     
     fun id(N,p,i) = i
     fun checkEven(N,p,i) = if (p[i] % 2 == 0) 
                            then p[i] 
                            else null
     fun reducer(r1,r2) = if not (r2 == null)
                          then r2
                          else r1  
                          
     cnd terminate(r) = not (r == null) and r % 2 == 0
                          
     PCR FirstEven(N):
       par
         p = produce id N
         forall p
           c = consume checkEven N p
         r = reduce terminate reducer 0 c
   ----------------------------------------------------------
*)

EXTENDS PCRFirstEvenTypes, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

id(x, p, i) == i

checkEven(x, p, i) == IF p[i].v % 2 = 0 THEN p[i].v ELSE Null

reducer(r1, r2) == IF r2 # Null THEN r2 ELSE r1

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 0
upperBnd(x) == x
step(i)     == i + 1
eCnd(r)     == r # Null /\ r % 2 = 0
\*eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpace WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)
                      
initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               ret |-> Null,
               ste |-> "OFF"]  

pre(x) == TRUE

----------------------------------------------------------------------------

(* 
   Producer action
   
   FXML:  forall i \in Range(0,N,Step)
            p[i] = id N               
   
   PCR:   p = produce id N
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> id(in(I), v_p(I), i), r |-> 0]]         
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))
                                          
(* 
   Consumer action
   
   FXML:  forall j \in Dom(p)
            c[j] = checkEven N p[j]

   PCR:   c = consume checkEven N p
*)
C(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1, 
         ![I].v_c[i]   = [v |-> checkEven(in(I), v_p(I), i), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce reducer 0 c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)    
    /\ ~ read(v_c(I), i)
    /\ LET newRet == reducer(out(I), v_c(I)[i].v)
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
   PCR FirstEven step at index I 
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
\* Last modified Mon Nov 09 21:54:24 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
