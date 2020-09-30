------------------------- MODULE PCRIterationSpace --------------------------

(*
   Iteration space for PCR.
*)

LOCAL INSTANCE Naturals

VARIABLES map, i_p

CONSTANTS InType,
          CtxIdType,
          IndexType,
          VarPType,
          VarCType,
          VarRType,    
          NULL
          
LOCAL INSTANCE PCRBase

CONSTANTS lowerBnd(_),
          upperBnd(_),
          step(_),
          eCnd(_)

range(start, end, stp(_)) ==
  LET f[i \in Nat] == 
        IF i <= end
        THEN {i} \union f[step(i)]
        ELSE {}    
  IN  f[start]  

\* Any PCR have an iteration space: a set of indexes  
iterator(I) == range(lowerBnd(in(I)), upperBnd(in(I)), step)

bound(I) == i_p \in iterator(I)    

cDone(I, i) == \A j \in iterator(I)\{i} : /\ written(v_c(I), j) 
                                          /\ read(v_c(I), j)

\* Start action         
Start(I) == map' = [map EXCEPT ![I].ste = "RUN"] 

\* Terminate if Eureka condition holds 
Eureka(I) == 
  \E i \in iterator(I) :
    /\ written(v_c(I), i)
    /\ read(v_c(I), i)
    /\ eCnd(out(I))
    /\ map' = [map EXCEPT ![I].ste = "END"]

\* Terminate if iteration space is empty      
Quit(I) == /\ iterator(I) = {} 
           /\ map' = [map EXCEPT ![I].ste = "END"]     

=============================================================================
\* Modification History
\* Last modified Tue Sep 29 23:52:37 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
