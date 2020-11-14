------------------------- MODULE PCRIterationSpace2 -------------------------

(*
   Iteration space for PCR with two consumers.
*)

LOCAL INSTANCE Naturals

VARIABLES cm

CONSTANTS InType,
          CtxIdType,
          IndexType,
          VarPType,
          VarC1Type,
          VarC2Type,
          VarRType,
          Undef
          
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

\* Terminate if iteration space is empty      
Quit(I) == /\ iterator(I) = {} 
           /\ cm' = [cm EXCEPT ![I].ste = "END"]     

=============================================================================
\* Modification History
\* Last modified Tue Nov 10 23:18:25 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
