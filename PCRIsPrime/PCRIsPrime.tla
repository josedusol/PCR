--------------------------- MODULE PCRIsPrime -----------------------------

(*
   PCR IsPrime
   
   ----------------------------------------------------------
     fun divisors, notDivides, and
     
     fun divisors(F,p,i) = i
     fun notDivides(F,p,j) = not (F % p[j] == 0)
     fun and(a,b) = a && b 
     
     fun lbnd divisors = 2 
     fun ubnd divisors = lambda x. Sqrt(x)
     fun step divisors = lambda x. 2*x - 1
   
     PCR IsPrime(F):
       par
         p = produceSeq divisors F
         forall p
           c = consume notDivides p F 
         r = reduce and (F > 1) c
   ----------------------------------------------------------
*)

EXTENDS PCRBase, Sequences

LOCAL INSTANCE TLC

InitCtx(input) == [in  |-> input,
                   i_p |-> LowerBnd(input),
                   v_p |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   v_c |-> [n \in IndexType |-> [v |-> NULL, r |-> 0]],
                   ret |-> input > 1,
                   ste |-> OFF]

----------------------------------------------------------------------------

(* 
   Basic functions that should be defined in host language                            
*)

divisors(x, p, i) == i
   
notDivides(x, p, j) == ~ (x % p[j].v = 0)

and(old, new) == old /\ new 

----------------------------------------------------------------------------
                                                  
(* 
   Producer action
   
   FXML:  for (j=LowerBnd(F); j < UpperBnd(F); Step(j))
            p[j] = j             
   
   PCR:   p = produceSeq divisors F                            
*)
P(i) == 
  /\ Bound(i) 
  /\ map' = [map EXCEPT 
       ![i].v_p[i_p(i)] = [v |-> divisors(in(i), v_p(i), i_p(i)), r |-> 0],
       ![i].i_p         = Step(@)]         
\*  /\ PrintT("P" \o ToString(i) \o " : " \o ToString(v_p(i)[j].v'))           

(* 
   Consumer action
   
   FXML:  forall j \in Dom(v_p)
            v_c[j] = count L j 

   PCR:   v_c = consume isDiv p F
*) 
C(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_p(i), j)
    /\ ~ Read(v_p(i), j)
    /\ ~ Written(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].v_p[j].r = @ + 1,
         ![i].v_c[j]   = [v |-> notDivides(in(i), v_p(i), j), r |-> 0] ]               
\*    /\ PrintT("C" \o ToString(j) \o " : P" \o ToString(j) 
\*                  \o " con v=" \o ToString(v_p(i)[j].v))       

(* 
   Reducer action
   
   FXML:  forall i \in Dom(v_p)
            r[j+1] = r[j] && i 

   PCR:   r = reduce and true v_c
*)
R(i) == 
  \E j \in Iterator(i) :
    /\ Written(v_c(i), j)    
    /\ ~ Read(v_c(i), j)
    /\ map' = [map EXCEPT 
         ![i].ret      = and(@, v_c(i)[j].v),
         ![i].v_c[j].r = @ + 1,
         ![i].ste      = IF CDone(i, j) THEN END ELSE @]                                                                     
\*    /\ IF CDone(i, j)
\*       THEN PrintT("IsPrime: in= " \o ToString(in(i)) 
\*                                   \o " ret= " \o ToString(Out(i)'))
\*       ELSE TRUE    
     
Next(i) == 
  \/ /\ Off(i) 
     /\ Start(i)
  \/ /\ Running(i) 
     /\ \/ P(i) 
        \/ C(i) 
        \/ R(i)
        \/ Quit(i)      

=============================================================================
\* Modification History
\* Last modified Wed Sep 09 20:13:31 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
