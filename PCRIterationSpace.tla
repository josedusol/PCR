------------------------- MODULE PCRIterationSpace --------------------------

(*
   Iteration space for PCR.
*)

LOCAL INSTANCE Naturals

VARIABLE map

CONSTANTS InType,
          CtxIdType,
          IndexType,
          VarPType,
          VarCType,
          VarRType,       
          NULL
          
LOCAL INSTANCE PCRBase

CONSTANTS LowerBnd(_),
          UpperBnd(_),
          Step(_)

range(start, end, step(_)) ==
  LET F[i \in Nat] == 
        IF i <= end
        THEN {i} \union F[step(i)]
        ELSE {}    
  IN  F[start]  

\* Any PCR have an iteration space: a set of indexes  
Iterator(I) == range(LowerBnd(in(I)), UpperBnd(in(I)), Step)

Bound(I) == i_p(I) \in Iterator(I)    

CDone(I, i) == \A j \in Iterator(I)\{i} : Read(v_c(I), j)

\* Quit action: if iteration space is empty PCR should terminate        
Quit(I) == /\ Iterator(I) = {} 
           /\ map' = [map EXCEPT ![I].ste = "END"]     

=============================================================================
\* Modification History
\* Last modified Sat Sep 26 00:21:35 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
