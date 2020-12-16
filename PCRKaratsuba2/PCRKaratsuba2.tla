-------------------------- MODULE PCRKaratsuba2 ----------------------------

(*
   PCR Karatsuba2 
   
   ---------------------------------------------------------------
     fun iterDivide, divide, isBase, base, conquer
     
     fun iterDivide(X,Y,p,i) = divide(X,Y)[i]
     
     fun divide(X,Y) = [ [x0, y0],
                         [x1 + x0, y1 + y0],
                         [x1, y1] ]
     
     fun subproblem(X,Y,p,i) = if   isBase(X,Y,p,i)
                               then base(X,Y,p,i)
                               else Karatsuba2(X,Y)
   
     fun computeA(X,Y,c1,i) = z2*10^(2*m)
     
     fun computeB(X,Y,c1,i) = (z1-z2-z0)*10^m + z0
   
     fun conquer(X,Y,o,c2,c3,i) = c2[i] + c3[i]
   
     dep c1(3) -> c2(i) 
     dep c1    -> c3(i) 
          
     PCR Karatsuba2(X, Y)
       par
         p = produce iterDivide X Y
         forall p
           c1 = consume subproblem X Y p
           c2 = consume computeA X Y c1
           c3 = consume computeB X Y c1
         r = reduce 0 conquer c2 c3
   ---------------------------------------------------------------  
*)

EXTENDS PCRKaratsuba2Types, PCRBase3, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

max(x, y) == IF x >= y THEN x ELSE y

isBaseCase(x, y) == x < 10 \/ y < 10

divide(x, y) == 
  IF isBaseCase(x, y)
  THEN << <<x,y>>, <<x,y>>, <<x,y>> >>
  ELSE LET  mx == max(Len(ToString(x)), Len(ToString(y)))
            m  == mx \div 2              \* Decompose x and y:
            x1 == x \div 10^m            \*   x = x1*10^m + x0
            x0 == x %    10^m            \*   y = y1*10^m + y0
            y1 == y \div 10^m               
            y0 == y %    10^m            \* Produce three sub-products:
        IN << <<x0, y0>>,                \*   z0 = x0 * y0 
              <<x1 + x0, y1 + y0>>,      \*   z1 = (x1 + x0) * (y1 + y0)
              <<x1, y1>>                 \*   z2 = x1 * y1
           >>    
                                    
iterDivide(x, p, I, i) == divide(x[1], x[2])[i]

base(x, p, I, i) == x[1] * x[2]

isBase(x, p, I, i) == isBaseCase(x[1], x[2]) 

computeA(x, p, c1, I, i) == 
  IF isBaseCase(x[1], x[2])
  THEN 0
  ELSE LET  mx == max(Len(ToString(x[1])), Len(ToString(x[2])))
            m  == mx \div 2 
            z2 == c1[3].v
       IN z2*10^(2*m)

computeB(x, p, c1, I, i) ==
  IF isBaseCase(x[1], x[2])
  THEN 0
  ELSE LET  mx == max(Len(ToString(x[1])), Len(ToString(x[2])))
            m  == mx \div 2 
            z0 == c1[1].v
            z1 == c1[2].v
            z2 == c1[3].v
       IN (z1-z2-z0)*10^m + z0 

conquer(x, o, c1, c2, c3, I, i) == 
  IF isBaseCase(x[1], x[2])
  THEN c1[i].v
  ELSE c2[i].v + c3[i].v 

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 1
upperBnd(x) == Len(divide(x[1], x[2]))
step(i)     == i + 1  
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpace3 WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

r0(x) == [v |-> 0, r |-> 0]

initCtx(x) == [in   |-> x,
               v_p  |-> [i \in IndexType |-> Undef],
               v_c1 |-> [i \in IndexType |-> Undef],
               v_c2 |-> [i \in IndexType |-> Undef],
               v_c3 |-> [i \in IndexType |-> Undef],
               v_r  |-> [i \in IndexType |-> r0(x)],             
               i_r  |-> lowerBnd(x),
               ste  |-> "OFF"] 

pre(x) == TRUE

----------------------------------------------------------------------------
            
(* 
   Producer action

   PCR:   p = produce iterDivide X Y                              
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> iterDivide(in(I), v_p(I), I, i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer 1 non-recursive action
*)
C1_base(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c1(I), i)
    /\ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r  = @ + 1,
         ![I].v_c1[i]   = [v |-> base(in(I), v_p(I), I, i), r |-> 0] ]               
\*    /\ PrintT("C1_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                        \o " con v=" \o ToString(v_c1(I)[i].v'))
 
(*
   Consumer 1 recursive call action
*)
C1_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ wellDef(I \o <<i>>)
    /\ ~ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT
         ![I].v_p[i].r = @ + 1,
         ![I \o <<i>>] = initCtx(v_p(I)[i].v) ]              
\*    /\ PrintT("C1_call" \o ToString(I \o <<i>>) 
\*                        \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer 1 recursive end action
*)
C1_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)    
     /\ ~ written(v_c1(I), i)
     /\ wellDef(I \o <<i>>)
     /\ finished(I \o <<i>>)   
     /\ cm' = [cm EXCEPT 
          ![I].v_c1[i] = [v |-> out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C1_ret" \o ToString(I \o <<i>>) 
\*                        \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                        \o " : ret= " \o ToString(Out(I \o <<i>>)))                

(*
   Consumer 1 action
*)
C1(I) == \/ C1_base(I)
         \/ C1_call(I) 
         \/ C1_ret(I)  

(*
   Consumer 2 action
*)
C2(I) ==
  \E i \in iterator(I) :
    /\ written(v_c1(I), 3)          \* dep c1(3) -> c2(i)
    /\ ~ written(v_c2(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_c1[3].r = @ + 1, 
         ![I].v_c2[i]   = [v |-> computeA(in(I), v_p(I), v_c1(I), I, i), r |-> 0] ]                                            
\*    /\ PrintT("C2" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                   \o " con v=" \o ToString(v_c2(I)[i].v'))    

(*
   Consumer 3 action
*)
C3(I) ==
  \E i \in iterator(I) :
    /\ \A j \in iterator(I) : written(v_c1(I), j)      \* dep c1 -> c3(i)
    /\ ~ written(v_c3(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_c1[i].r = @ + 1, 
         ![I].v_c3[i]   = [v |-> computeB(in(I), v_p(I), v_c1(I), I, i), r |-> 0] ]                                            
\*    /\ PrintT("C3" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                   \o " con v=" \o ToString(v_c3(I)[i].v'))    
  
(* 
   Reducer action
   
   PCR:  r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c2(I), i)
    /\ written(v_c3(I), i)   
    /\ pending(I, i)
    /\ LET newOut == conquer(in(I), out(I), v_c1(I), v_c2(I), v_c3(I), I, i)
           endSte == rDone(I, i) \/ eCnd(newOut)
       IN  cm' = [cm EXCEPT 
             ![I].v_c1[i].r = @ + 1,
             ![I].v_c2[i].r = @ + 1,
             ![I].v_c3[i].r = @ + 1,
             ![I].v_r[i]    = [v |-> newOut, r |-> 1],
             ![I].i_r       = i,
             ![I].ste       = IF endSte THEN "END" ELSE @]                                                                            
\*          /\ IF endSte
\*             THEN PrintT("R" \o ToString(I \o <<i>>) 
\*                             \o " : in= "  \o ToString(in(I))    
\*                             \o " : ret= " \o ToString(out(I)')) 
\*             ELSE TRUE              

(* 
   PCR Karatsuba2 step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)
        \/ C1(I)  
        \/ C2(I) 
        \/ C3(I)
        \/ R(I)  
        \/ Quit(I)
 
=============================================================================
\* Modification History
\* Last modified Wed Dec 16 15:13:48 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
