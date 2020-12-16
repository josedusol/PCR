---------------------------- MODULE PCRMerge -------------------------------

(*
   PCR Merge
   
   ---------------------------------------------------------------
     fun iterDivide, divide, isBase, base, conquer, binarySearch
     
     fun iterDivide(X,Y,p,i) = divide(X,Y)[i]
     
     fun divide(X,Y) = [ [X1,Y1],
                         [X2,Y2] ]
     
     fun subproblem(X,Y,p,i) = if   isBase(X,Y,p,i)
                               then base(X,Y,p,i)
                               else Merge(X,Y)
   
     fun conquer(o, c, i) = c[1] ++ c[2]
     
     dep c -> r(i)
   
     PCR Merge(X, Y)
       par
         p = produce iterDivide X Y
         forall p
           c = consume subproblem X Y p
         r = reduce [] conquer c
   ---------------------------------------------------------------  
*)

EXTENDS PCRMergeTypes, PCRBase, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

isOrdered(s) == \/ Len(s) <= 1
                \/ LET n == 2..Len(s) IN \A k \in n: s[k-1] <= s[k] 

\* Return position where element "e" should be in the ordered seq
binarySearch(seq, e) ==
  LET f[s \in Seq(Elem)] == 
        IF s = << >> 
        THEN -1
        ELSE LET m == (Len(s) + 1) \div 2
             IN  CASE  e = s[m]  ->  m
                   []  e < s[m]  ->  f[SubSeq(s, 1, m-1)]
                   []  e > s[m]  ->  LET p == f[SubSeq(s, m+1, Len(s))]
                                     IN  IF p > -1 THEN p + m ELSE m - p
  IN f[seq] 

isBaseCase(x1, x2) == Len(x1) <= 1 /\ Len(x2) <= 1

divide(x1, x2) == 
  LET X == IF Len(x1) >= Len(x2) THEN x1 ELSE x2      \* if necessary, swap to make Len(X) <= Len(Y)
      Y == IF Len(x1) >= Len(x2) THEN x2 ELSE x1      \*
  IN IF isBaseCase(X, Y) 
     THEN << <<X,Y>> >>
     ELSE LET X_m == (Len(X) + 1) \div 2                          \* 1. Split X in two parts X1 and X2
              X1  == SubSeq(X, 1, X_m) 
              X2  == SubSeq(X, X_m+1, Len(X)) 
              k   == X2[1]                                        \* 2. Take X2[1] and search its position in Y
              Y_m == binarySearch(Y, k)
              Y1  == CASE Y_m = -1     -> << >>                   \* 3. Split Y in that position
                       [] Y_m > Len(Y) -> Y
                       [] OTHER        -> SubSeq(Y, 1, Y_m-1)                          
              Y2  == CASE Y_m = -1     -> Y                        
                       [] Y_m > Len(Y) -> << >>
                       [] OTHER        -> SubSeq(Y, Y_m, Len(Y))   
          IN  << <<X1,Y1>>, <<X2,Y2>> >>                          \* Produce two sub-merges

iterDivide(x, p, I, i) == divide(x[1], x[2])[i]

base(x, p, I, i) == 
  LET X == p[i].v[1]  
      Y == p[i].v[2]
  IN IF Len(Y) = 0 
     THEN X 
     ELSE IF X[1] <= Y[1]       \* Order two unitary lists
          THEN <<X[1],Y[1]>>  
          ELSE <<Y[1],X[1]>> 

isBase(x, p, I, i) == isBaseCase(p[i].v[1], p[i].v[2])

conquer(x, o, c, I, i) == 
  IF isBaseCase(x[1], x[2]) 
  THEN c[1].v
  ELSE c[1].v \o c[2].v

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 1
upperBnd(x) == Len(divide(x[1], x[2]))
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

r0(x) == [v |-> <<>>, r |-> 0]

initCtx(x) == [in  |-> x,
               v_p |-> [i \in IndexType |-> Undef],
               v_c |-> [i \in IndexType |-> Undef],
               v_r |-> [i \in IndexType |-> r0(x)],             
               i_r |-> lowerBnd(x),
               ste |-> "OFF"] 

pre(x) == isOrdered(x[1]) /\ isOrdered(x[2])

----------------------------------------------------------------------------
            
(* 
   Producer action

   PCR:  p = produce iterDivide X Y                              
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
\*    /\ PrintT("C_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                       \o " con v=" \o ToString(v_p(I)[i].v))

(*
   Consumer recursive call action
*)
C_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ wellDef(I \o <<i,2>>)
    /\ ~ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r   = @ + 1,
         ![I \o <<i,2>>] = initCtx(v_p(I)[i].v) ]              
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer recursive end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)   
     /\ ~ written(v_c(I), i)
     /\ wellDef(I \o <<i,2>>)
     /\ finished(I \o <<i,2>>)   
     /\ cm' = [cm EXCEPT 
          ![I].v_c[i] = [v |-> out(I \o <<i,2>>), r |-> 0]]  
\*     /\ PrintT("C_ret" \o ToString(I \o <<i>>) 
\*                       \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                       \o " : ret= " \o ToString(Out(I \o <<i>>)))                

(*
   Consumer action
   
   PCR:  c = consume subproblem X Y p
*)
C(I) == \/ C_base(I)
        \/ C_call(I) 
        \/ C_ret(I)           

(* 
   Reducer action
   
   PCR:  c = reduce [] conquer c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ \A j \in iterator(I) : written(v_c(I), j)         \* dep c -> r(i)
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
   PCR Merge step at index I 
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
\* Last modified Wed Dec 16 16:07:44 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
