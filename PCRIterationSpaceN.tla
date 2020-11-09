------------------------- MODULE PCRIterationSpaceN -------------------------

(*
   Iteration space for PCR.
*)

LOCAL INSTANCE Naturals

VARIABLES cm

CONSTANTS InType,
          CtxIdType,
          IndexType,
          VarPType,
          VarCType,
          VarRType
          
LOCAL INSTANCE PCRBase

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

cDone(I, i) == \A j \in iterator(I)\{i} : /\ written(v_c(cLen, I), j) 
                                          /\ read(v_c(cLen, I), j)

\* Start action         
Start(I) == cm' = [cm EXCEPT ![I].ste = "RUN"] 

\* Terminate if Eureka condition holds 
\*Eureka(I) == 
\*  \E i \in iterator(I) :
\*    /\ written(v_c(cLen, I), i)
\*    /\ read(v_c(cLen, I), i)
\*    /\ eCnd(out(I))
\*    /\ map' = [map EXCEPT ![I].ste = "END"]

\* Terminate if iteration space is empty      
Quit(I) == /\ iterator(I) = {} 
           /\ cm' = [cm EXCEPT ![I].ste = "END"]   

=============================================================================
\* Modification History
\* Last modified Thu Nov 05 01:52:23 UYT 2020 by josedu
\* Created Wed Oct 21 14:41:43 UYT 2020 by josedu
