-------------------------- MODULE PCRMapFilter -----------------------------

(*
   PCR Fib
   
   ----------------------------------------------------------
     fun fib, checkLast, projectRed
     
     lbnd all = lambda x. 1
     ubnd all = lambda x. len x
     step all = lambda i. i + 1
     
     fun predicate(x) = x < 2
     
     fun all(L,p,i) = L[i]
     fun map(L,p,i) = if predicate(p[i]) then true else false 
     fun prefixList(L,p,c1,i) =
       if c1[i] 
       then if i > 1
            then createL(i-1) ++ [p[i]]
            else [p[i]]
       else []
     
     fun merge(l1,l2)
       if  l1 == []
       then l2
       else if l2 == []
           then l1
           else if head l1 == null and head l2 == null
                then [null] ++ merge(tail s1, tail s2)                      
                else if head l1 != null and 
                     then [head l1] ++ merge(tail s1, tail s2) 
                     else if head l2 != null   
                          then [head l2] ++ merge(tail s1, tail s2)
                          else 
                
                then [head l1] ++ merge(tail s1, s2)  
                else [head l2] ++ merge(s1, tail s2)                
 
     \\ dep c1(i) -> c2(i)
     dep c1(i-1) -> c2(i)                    \\  solo un written
     dep c1(..i) -> c2(i)                    \\  \A j <= i : c1(j) -> c2(i)
     dep c1(i..) -> c2(i)                    \\  \A j >= i : c1(j) -> c2(i)
     dep c1(i-5..i+3) -> c2(i)               \\  \A i-5 >= j <= i+3 : c1(j) -> c2(i)             
 
 
     dep c1(i-1) -> r(i)               \\
     dep c2(i-3) -> r(i)
 
     fun join(ac, c1, c2, i) = c1[i] ....  c2[i]
 
     PCR Filter(L):
       par
         p = produce all L
         forall p
           par
             c1 = consume map L p
             c2 = consume prefixSum L p
         r = reduce join [] c1 c2
   ----------------------------------------------------------
*)

\*[3,5,2]
\*
\*c1 = [i: 1, v: 3]   c1 = NULL  c3 = [i: 3, v: 2]
\* 
\*[] 


\*(x1 + x2) + x3 
\*
\*<<x1, x1 + x2, (x1 + x2) + x3 >>


EXTENDS PCRMapFilterTypes, PCRBase2, TLC

VARIABLE im

----------------------------------------------------------------------------

(* 
   Basic functions                     
*)

all(x, p, i) == x[i]

predicate(x) == x < 2

mapp(x, p, i) == IF predicate(p[i].v) THEN TRUE ELSE FALSE

createL(len) ==
  LET f[n \in Nat] ==
        IF n = 0
        THEN << >>
        ELSE <<Null>> \o f[n-1]
  IN f[len]

prefixList(x, p, c1, i) == 
  IF c1[i].v 
  THEN IF i > 1
       THEN createL(i-1) \o << p[i].v >>
       ELSE << p[i].v >>        
  ELSE << >>

merge(seq1, seq2) ==
  LET F[s1, s2 \in Seq(Nat \union {Null})] ==
        IF s1 = << >> 
        THEN s2 
        ELSE IF s2 = << >> 
             THEN s1 
             ELSE CASE Head(s1) = Null /\ Head(s2) = Null -> 
                         <<Null>> \o F[Tail(s1), Tail(s2)]
                    [] Head(s1) # Null /\ Head(s2) = Null -> 
                         <<Head(s1)>> \o F[Tail(s1), Tail(s2)]
                    [] Head(s1) = Null /\ Head(s2) # Null -> 
                         <<Head(s2)>> \o F[Tail(s1), Tail(s2)]                  
  IN F[seq1, seq2] 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 1
upperBnd(x) == Len(x)
step(i)     == i + 1
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpace2 WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

i_p(I)   == im[I]
IndexMap == [CtxIdType -> IndexType \union {Undef}]  

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)
                      
initCtx(x) == [in   |-> x,
               v_p  |-> [i \in IndexType |-> Undef],
               v_c1 |-> [i \in IndexType |-> Undef],
               v_c2 |-> [i \in IndexType |-> Undef],
               ret  |-> << >>,
               ste  |-> "OFF"]  

pre(x) == TRUE

----------------------------------------------------------------------------

(* 
   Producer action
   
   FXML:  forall i \in 1..Len(L)
            p[i] = all L          
   
   PCR:   p = produce all L                              
*)
P(I) == 
  \E i \in iterator(I) :
    /\ ~ written(v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i] = [v |-> all(in(I), v_p(I), i), r |-> 0]]       
\*  /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v')) 
                                          
(* 
   Consumer 1 action
   
   FXML:  forall i \in Dom(p)
            c1[i] = map L p

   PCR:   c1 = consume map L p
*)
C1(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
\*    /\ ~ read(v_p(I), i)
    /\ ~ written(v_c1(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = 1, 
         ![I].v_c1[i]  = [v |-> mapp(in(I), v_p(I), i), r |-> 0]]                         
\*    /\ PrintT("C1" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                   \o " con v=" \o ToString(v_p(I)[i].v))  

(* 
   Consumer 2 action
   
   FXML:  forall i \in Dom(p)
            c2[i] = filter L c1

   PCR:   c2 = consume filter L c1
*)
C2(I) == 
  \E i \in iterator(I) :
    /\ written(v_c1(I), i-1)     \* dep c1(i-1) -> c2(i)
    \*/\ ~ read(v_c1(I), i-1)      \* ...
    
    /\ written(v_c1(I), i)       \* dep c1(i) -> c2(i)
   \* /\ ~ read(v_c1(I), i)        \* ...
    
    /\ ~ written(v_c2(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_c1[i].r = 1, 
         ![I].v_c2[i]   = [v |-> prefixList(in(I), v_p(I), v_c1(I), i), r |-> 0]]                         
\*    /\ PrintT("C2" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                   \o " con v=" \o ToString(v_c1(I)[i].v))  

(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce ++ [] c2
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c2(I), i)    
    /\ ~ read(v_c2(I), i)
    /\ LET newRet == merge(out(I), v_c2(I)[i].v)
           endSte == cDone(I, i) \/ eCnd(newRet)
       IN  cm' = [cm EXCEPT 
             ![I].ret       = newRet,
             ![I].v_c2[i].r = @ + 1,
             ![I].ste       = IF endSte THEN "END" ELSE @]
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE    

(* 
   PCR Fib step at index I 
*)     
Next(I) == 
  \/ /\ state(I) = "OFF"
     /\ Start(I)
     /\ UNCHANGED im
  \/ /\ state(I) = "RUN"
     /\ \/ P(I) 
        \/ C1(I)
        \/ C2(I)
        \/ R(I)
        \/ Quit(I)
     /\ UNCHANGED im      

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 02:38:17 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:29:48 UYT 2020 by josed
\* Created Mon Jul 06 13:22:55 UYT 2020 by josed
