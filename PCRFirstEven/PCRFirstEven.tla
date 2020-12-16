-------------------------- MODULE PCRFirstEven -----------------------------

(*
   PCR FirstEven
   
   ----------------------------------------------------------
     fun id, checkEven, ret
     
     lbnd projectProd = lambda x. 0 
     ubnd projectProd = lambda x. x
     
     fun id(N,p,i) = i
     fun checkEven(N,p,i) = if (p[i] % 2 == 0) 
                            then p[i] 
                            else null
     fun ret(X,o,c,i) = c[i] 
                          
     cnd terminate(o) = not (o == null) and o % 2 == 0
                          
     PCR FirstEven(N):
       par
         p = produce id N
         forall p
           c = consume checkEven N p
         r = reduce terminate ret null c
   ----------------------------------------------------------
*)

EXTENDS PCRFirstEvenTypes, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

id(x, p, I, i) == i

checkEven(x, p, I, i) == IF p[i].v % 2 = 0 THEN p[i].v ELSE Null

ret(x, o, c, I, i) == c[i].v

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

r0(x) == [v |-> Null, r |-> 0]

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
   
   FXML:  forall i \in Range(0,N,Step)
            p[i] = id N               
   
   PCR:   p = produce id N
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> id(in(I), v_p(I), I, i), r |-> 0]]         
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
         ![I].v_c[i]   = [v |-> checkEven(in(I), v_p(I), I, i), r |-> 0]]                         
\*    /\ PrintT("C" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                  \o " con v=" \o ToString(v_p(I)[i].v))  
   
(* 
   Reducer action
   
   FXML:  ...

   PCR:   c = reduce reducer 0 c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == ret(in(I), out(I), v_c(I), I, i)
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
\* Last modified Tue Dec 15 20:55:22 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
