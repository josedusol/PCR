-------------------------- MODULE PCRKaratsuba -----------------------------

(*
   PCR Karatsuba 
   
   ---------------------------------------------------------------
     fun iterDivide, divide, isBase, base, conquer, ret
     
     fun iterDivide(X,Y,p,i) = divide(X,Y)[i]
     
     fun divide(X,Y) = [ [x0, y0],
                         [x1 + x0, y1 + y0],
                         [x1, y1] ]
     
     fun subproblem(X,Y,p,i) = if   isBase(X,Y,p,i)
                               then base(X,Y,p,i)
                               else Karatsuba(X,Y)
   
     fun conquer(X,Y,c1,i) = (z2*10^(2*m)) + ((z1-z2-z0)*10^m) + z0 
   
     fun ret(r,z) = z
   
     dep c1(..i) -> c2(i)          \\ dep c1 -> c2(i)
     dep c1(i..) -> c2(i)       
   
     PCR Karatsuba(X, Y)
       par
         p = produce iterDivide X Y
         forall p
           par
             c1 = consume subproblem X Y p
             c2 = consume conquer X Y c1
         r = reduce ret 1 c2
   ---------------------------------------------------------------  
*)

EXTENDS PCRKaratsubaTypes, PCRBase2, TLC

----------------------------------------------------------------------------

(* 
   Basic functions                 
*)

max(x, y) == IF x >= y THEN x ELSE y

isBaseCase(x, y) == x < 10 \/ y < 10

divide(x, y) == 
  IF isBaseCase(x, y)
  THEN << <<x,y>> >>
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
                                    
iterDivide(x, y, p, i) == divide(x, y)[i]

base(x, y, p, i) == x * y

isBase(x, y, p, i) == isBaseCase(x, y)

conquer(x, y, c1, i) == 
  IF isBaseCase(x, y)
  THEN c1[1].v
  ELSE LET  mx == max(Len(ToString(x)), Len(ToString(y)))
            m  == mx \div 2 
            z0 == c1[1].v
            z1 == c1[2].v
            z2 == c1[3].v
       IN (z2*10^(2*m)) + ((z1-z2-z0)*10^m) + z0 
 
ret(r, z) == z

----------------------------------------------------------------------------

(* 
   Iteration space                 
*)

lowerBnd(x) == 1
upperBnd(x) == Len(divide(x[1], x[2]))
step(i)     == i + 1  
eCnd(r)     == FALSE
 
INSTANCE PCRIterationSpace2 WITH
  lowerBnd  <- lowerBnd,
  upperBnd  <- upperBnd,  
  step      <- step

----------------------------------------------------------------------------

(* 
   Initial conditions        
*)

initCtx(x) == [in   |-> x,
               v_p  |-> [i \in IndexType |-> Undef],
               v_c1 |-> [i \in IndexType |-> Undef],
               v_c2 |-> [i \in IndexType |-> Undef],
               ret  |-> 1,
               ste  |-> "OFF"] 

pre(x) == TRUE

----------------------------------------------------------------------------
            
(* 
   Producer action
   
   FXML:  forall i \in 1..Len(divide(B))
            p[j] = divide L             
   
   PCR:   p = produce divide L                              
*)
P(I) == 
  \E i \in iterator(I) : 
    /\ ~ written(v_p(I), i)         
    /\ cm' = [cm EXCEPT  
         ![I].v_p[i] = [v |-> iterDivide(in1(I), in2(I), v_p(I), i), r |-> 0] ]             
\*    /\ PrintT("P" \o ToString(I \o <<i>>) \o " : " \o ToString(v_p(I)[i].v'))                  

(*
   Consumer 1 non-recursive action
*)
C1_base(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ written(v_c1(I), i)
    /\ isBase(in1(I), in2(I), v_p(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_p[i].r = @ + 1,
         ![I].v_c1[i]  = [v |-> base(in1(I), in2(I), v_p(I), i), r |-> 0] ]               
\*    /\ PrintT("C1_base" \o ToString(i) \o " : P" \o ToString(i) 
\*                        \o " con v=" \o ToString(v_p(I)[i].v))
 
(*
   Consumer 1 recursive call action
*)
C1_call(I) == 
  \E i \in iterator(I) :
    /\ written(v_p(I), i)
    /\ ~ read(v_p(I), i)
    /\ ~ isBase(in1(I), in2(I), v_p(I), i)
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
     /\ read(v_p(I), i)       
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
    /\ \A j \in iterator(I) : j <= i => written(v_c1(I), j)       \* dep c1(..i) -> c2(i)
    /\ \A j \in iterator(I) : j >= i => written(v_c1(I), j)       \* dep c1(i..) -> c2(i)
    /\ ~ written(v_c2(I), i)
    /\ cm' = [cm EXCEPT 
         ![I].v_c1[i].r = @ + 1, 
         ![I].v_c2[i]   = [v |-> conquer(in1(I), in2(I), v_c1(I), i), r |-> 0] ]                                            
\*    /\ PrintT("C2" \o ToString(I \o <<i>>) \o " : P" \o ToString(i) 
\*                   \o " con v=" \o ToString(v_c2(I)[i].v'))         
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
    /\ written(v_c2(I), i)
    /\ ~ read(v_c2(I), i)
    /\ LET newRet == ret(out(I), v_c2(I)[i].v)
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
   PCR Karatsuba step at index I 
*)
Next(I) == 
  \/ /\ state(I) = "OFF" 
     /\ Start(I)
  \/ /\ state(I) = "RUN" 
     /\ \/ P(I)
        \/ C1(I)  
        \/ C2(I)  
        \/ R(I)  
        \/ Quit(I)
 
=============================================================================
\* Modification History
\* Last modified Fri Nov 20 23:07:19 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
