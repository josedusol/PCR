-------------------------- MODULE PCRKaratsuba1 ----------------------------

(*
   PCR Karatsuba1 
   
   ---------------------------------------------------------------
     fun iterDivide, divide, isBase, base, conquer
     
     fun iterDivide(X,Y,p,i) = divide(X,Y)[i]
     
     fun divide(X,Y) = [ [x0, y0],
                         [x1 + x0, y1 + y0],
                         [x1, y1] ]
     
     fun subproblem(X,Y,p,i) = if   isBase(X,Y,p,i)
                               then base(X,Y,p,i)
                               else Karatsuba1(X,Y)
   
     fun conquer(X,Y,o,c,i) = (z2*10^(2*m)) + ((z1-z2-z0)*10^m) + z0   
   
     dep c -> r(i)                \\same effect as: dep c(..i) -> r(i)
                                  \\                dep c(i..) -> r(i)       
     PCR Karatsuba1(X, Y)
       par
         p = produce iterDivide X Y
         forall p
             c = consume subproblem X Y p
         r = reduce conquer 1 c
   ---------------------------------------------------------------  
*)

EXTENDS PCRKaratsuba1Types, PCRBase, TLC

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
                                    
iterDivide(x, p, I, i) == divide(x[1], x[2])[i]

base(x, p, I, i) == p[i].v[1] * p[i].v[2]

isBase(x, p, I, i) == isBaseCase(p[i].v[1], p[i].v[2])

conquer(x, o, c, I, i) == 
  IF isBaseCase(x[1], x[2])
  THEN c[1].v
  ELSE LET  mx == max(Len(ToString(x[1])), Len(ToString(x[2])))
            m  == mx \div 2 
            z0 == c[1].v
            z1 == c[2].v
            z2 == c[3].v
       IN (z2*10^(2*m)) + ((z1-z2-z0)*10^m) + z0 

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

r0(x) == [v |-> 1, r |-> 0]

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
            p[j] = divide L             
   
   PCR:   p = produce divide L                              
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
    /\ ~ wellDef(I \o <<i>>)
    /\ ~ isBase(in(I), v_p(I), I, i)
    /\ cm' = [cm EXCEPT
         ![I].v_p[i].r = @ + 1,
         ![I \o <<i>>] = initCtx(v_p(I)[i].v) ]              
\*    /\ PrintT("C_call" \o ToString(I \o <<i>>) 
\*                       \o " : in= " \o ToString(v_p(I)[i].v))                                                                                                                                            

(*
   Consumer recursive end action
*)
C_ret(I) == 
  \E i \in iterator(I) :
     /\ written(v_p(I), i)    
     /\ ~ written(v_c(I), i)
     /\ wellDef(I \o <<i>>)
     /\ finished(I \o <<i>>)   
     /\ cm' = [cm EXCEPT 
          ![I].v_c[i] = [v |-> out(I \o <<i>>), r |-> 0]]  
\*     /\ PrintT("C1_ret" \o ToString(I \o <<i>>) 
\*                        \o " : in= "  \o ToString(in(I \o <<i>>))    
\*                        \o " : ret= " \o ToString(Out(I \o <<i>>)))                

(*
   Consumer action
*)
C(I) == \/ C_base(I)
        \/ C_call(I) 
        \/ C_ret(I)  
  
(* 
   Reducer action
   
   FXML:  ...

   PCR:   r = reduce conquer [] c
*)
R(I) == 
  \E i \in iterator(I) :
\*    /\ \A j \in iterator(I) : j <= i => written(v_c(I), j)       \* dep c1(..i) -> c2(i)
\*    /\ \A j \in iterator(I) : j >= i => written(v_c(I), j)       \* dep c1(i..) -> c2(i)
    /\ \A j \in iterator(I) : written(v_c(I), j)                   \* dep c -> r(i)
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
   PCR Karatsuba1 step at index I 
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
\* Last modified Tue Dec 15 20:56:41 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
