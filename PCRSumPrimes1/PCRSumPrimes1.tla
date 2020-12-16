--------------------------- MODULE PCRSumPrimes1 ---------------------------

(*
   PCR SumPrimes1
   
   ---------------------------------------------------------------------
     fun divide, isBase, base, conquer, isPrime
     
     fun iterDivide(L,p,i) = divide(L)[i]
     
     fun divide(L) = [ L[1..Len(L)/2],
                       L[(Len(L)/2)+1..Len(L)] ]
     
     fun subproblem(L,p,i) = if   isBase(L, p, i)
                             then base(L, p, i)
                             else SumPrimes1(L)
   
     fun conquer(o, c, i) = o + c[i]
      
     PCR SumPrimes1(L):
       par
         p = produce iterDivide L
         forall p
           c = consume subproblem L p
         r = reduce conquer [] c
   ---------------------------------------------------------------------
*)

EXTENDS PCRSumPrimes1Types, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

divide(x) == LET mid == Len(x) \div 2
             IN  << SubSeq(x, 1, mid), 
                    SubSeq(x, mid+1, Len(x)) >>   

iterDivide(x, p, I, i) == divide(x)[i]

isPrime(n) == LET div(k,m) == \E d \in 1..m : m = k * d
              IN n > 1 /\ ~ \E m \in 2..n-1 : div(m, n)

base(x, p, I, i) == IF /\ p[i].v # << >> 
                       /\ isPrime(p[i].v[1])
                    THEN p[i].v[1] 
                    ELSE 0

isBase(x, p, I, i) == Len(p[i].v) <= 1

conquer(x, o, c, I, i) == o + c[i].v

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 1
upperBnd(x) == Len(divide(x))
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
   
   FXML:  forall i \in 1..Len(divide(B))
            p[i] = divide B             
   
   PCR:   p = produce divide B                            
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> iterDivide(in(I), v_p(I), I, i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer non-recursive action
*)
C_base(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c[i]   = [v |-> base(in(I), v_p(I), I, i), r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(base(in(I), v_p(I), i)))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ wellDef(I \o <<i>>)
    /\ ~ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I \o <<i>>] = initCtx(v_p(I)[i].v) ]
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(in(I \o <<i>>)'))                                                                                                                                            

(*
   Consumer recursive return action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)  
     /\ ~ written(v_c(I), i)
     /\ wellDef(I \o <<i>>)
     /\ finished(I \o <<i>>)   
     /\ cm' = [cm EXCEPT 
          ![I].v_c[i]= [v |-> out(I \o <<i>>), r |-> 0]]  
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

   PCR:   c = reduce [] conquer c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ pending(I, i)
    /\ LET newOut == conquer(in(I), out(I), v_c(I), I, i)
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
   PCR SumPrimes1 step at index I 
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
\* Last modified Tue Dec 15 21:01:38 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
