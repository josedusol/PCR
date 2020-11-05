--------------------------- MODULE PCRSumPrimes2 ---------------------------

(*
   PCR SumPrimes2
   
   ---------------------------------------------------------------------
     fun divide, isBase, base, conquer
     
     fun iterDivide(L,p,i) = divide(L)[i]
     
     fun divide(L) = [ L[1..Len(L)/2],
                       L[(Len(L)/2)+1..Len(L)] ]
     
     fun isBase(L,p,i) = Len p[i] <= 1
     
     fun base(L,p,i) = if p[i] != [] and IsPrime(p[i][1])
                       then p[i][1]
                       else 0
     
     fun subproblem(L,p,i) = if   isBase(L, p, i)
                             then base(L, p, i)
                             else SumPrimes(L)
   
     fun conquer(r1,r2) = r1 + r2
      
     PCR SumPrimes2(L):
       par
         p = produce iterDivide L
         forall p
           c = consume subproblem L p
         r = reduce conquer 0 c
         
     PCR IsPrime(N):
       par
         p = produce divisors N
         forall p
           c = consume notDivides N p
         r = reduce and (N > 1) c    
   ---------------------------------------------------------------------
*)

EXTENDS Typedef, PCRBase, TLC

VARIABLES cm2

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

isPrime == INSTANCE PCRIsPrime WITH
  InType    <- InType2,  
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  cm        <- cm2

divide(x) == LET mid == Len(x) \div 2
             IN  << SubSeq(x, 1, mid), 
                    SubSeq(x, mid+1, Len(x)) >>   

iterDivide(x, p, i) == divide(x)[i]

isBase(x, p, i) == Len(p[i].v) <= 1

conquer(r1, r2) == r1 + r2

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

initCtx(x) == [in  |-> x,
               v_p |-> [n \in IndexType |-> Undef],
               v_c |-> [n \in IndexType |-> Undef],
               ret |-> 0,
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
         ![I].v_p[i] = [v |-> iterDivide(in(I), v_p(I), i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  


(*
   Consumer recursive call action
*)
C_isBase_1(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
\*    /\ ~ read(v_p(I), i)
    /\ Len(v_p(I)[i].v) <= 1        \* isBase(in(I), v_p(I), i)
    /\ ~ (v_p(I)[i].v # << >>)
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> 0 , r |-> 0] ]
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(in(I \o <<i>>)')) 

(*
   Consumer recursive call action
*)
C_isBase_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ Len(v_p(I)[i].v) <= 1        \* isBase(in(I), v_p(I), i)
    /\ v_p(I)[i].v # << >>
    /\ cm'  = [cm  EXCEPT 
         ![I].v_p[i].r = @ + 1]    
    /\ cm2' = [cm2 EXCEPT 
         ![I \o <<i>>] = isPrime!initCtx((v_p(I)[i].v)[1]) ]
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(in(I \o <<i>>)')) 

(*
   Consumer non-recursive action
*)
C_isBase_ret1(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ Len(v_p(I)[i].v) <= 1        \* isBase(in(I), v_p(I), i)  
    /\ v_p(I)[i].v # << >> 
    /\ isPrime!wellDef(I \o <<i>>)
    /\ isPrime!finished(I \o <<i>>)
    /\ isPrime!out(I \o <<i>>)
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> (v_p(I)[i].v)[1], r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(base(in(I), v_p(I), i)))

(*
   Consumer non-recursive action
*)
C_isBase_ret2(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ read(v_p(I), i)
    /\ ~ written(v_c(I), i)
    /\ Len(v_p(I)[i].v) <= 1        \* isBase(in(I), v_p(I), i)  
    /\ v_p(I)[i].v # << >>
    /\ isPrime!wellDef(I \o <<i>>)
    /\ isPrime!finished(I \o <<i>>)
    /\ ~ isPrime!out(I \o <<i>>)
    /\ cm' = [cm EXCEPT 
         ![I].v_c[i] = [v |-> 0, r |-> 0] ]               
\*    /\ PrintT("C_base" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(base(in(I), v_p(I), i)))

(*
   Consumer recursive call action
*)
C_noBase_call(I) == 
  \E i \in iterator(I):
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ ~ (Len(v_p(I)[i].v) <= 1)   \* ~ isBase(in(I), v_p(I), i)  
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I \o <<i>>] = initCtx(v_p(I)[i].v) ]
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(in(I \o <<i>>)'))                                                                                                                                            

(*
   Consumer recursive return action
*)
C_noBase_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)
     /\ read(v_p(I), i)       
     /\ ~ written(v_c(I), i)
     /\ wellDef(I \o <<i>>)
     /\ finished(I \o <<i>>)
     /\ cm' = [cm EXCEPT 
          ![I].v_c[i] = [v |-> out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(out(I \o <<i>>)))                

(*
   Consumer action
*)
C(I) == \/ C_isBase_1(I)     /\ UNCHANGED cm2
        \/ C_isBase_call(I)
        \/ C_isBase_ret1(I)  /\ UNCHANGED cm2
        \/ C_isBase_ret2(I)  /\ UNCHANGED cm2       
        \/ C_noBase_call(I)  /\ UNCHANGED cm2
        \/ C_noBase_ret(I)   /\ UNCHANGED cm2
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ ~ read(v_c(I), i)
    /\ LET newRet == conquer(out(I), v_c(I)[i].v)
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
   PCR NQueensFirst step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
     /\ UNCHANGED cm2
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)    /\ UNCHANGED cm2
        \/ C(I) 
        \/ R(I)    /\ UNCHANGED cm2
        \/ Quit(I) /\ UNCHANGED cm2   
 
=============================================================================
\* Modification History
\* Last modified Thu Oct 29 18:03:37 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
