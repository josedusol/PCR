------------------------- MODULE PCRIterationSpace2 -------------------------

(*
   Iteration space for PCR.
*)

LOCAL INSTANCE Naturals

VARIABLES cm

CONSTANTS InType,
          CtxIdType,
          IndexType,
          VarPType,
          VarC1Type,
          VarC2Type,
          VarRType
          
LOCAL INSTANCE PCRBase2

CONSTANTS lowerBnd(_),
          upperBnd(_),
          step(_)

range(start, end, stp(_)) ==
  LET f[i \in Nat] == 
        IF i <= end
        THEN {i} \union f[stp(i)]
        ELSE {}    
  IN  f[start]  

\* Any PCR have an iteration space: a set of indexes  
iterator(I) == range(lowerBnd(in(I)), upperBnd(in(I)), step)

cDone(I, i) == \A j \in iterator(I)\{i} : /\ written(v_c2(I), j) 
                                          /\ read(v_c2(I), j)

\* Start action         
Start(I) == cm' = [cm EXCEPT ![I].ste = "RUN"] 

\* Terminate if Eureka condition holds 
\*Eureka(I) == 
\*  \E i \in iterator(I) :
\*    /\ written(v_c2(I), i)
\*    /\ read(v_c2(I), i)
\*    /\ eCnd(out(I))
\*    /\ map' = [map EXCEPT ![I].ste = "END"]

\* Terminate if iteration space is empty      
Quit(I) == /\ iterator(I) = {} 
           /\ map' = [map EXCEPT ![I].ste = "END"]     

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 19:32:48 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
