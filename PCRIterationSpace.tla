------------------------- MODULE PCRIterationSpace --------------------------

(*
   Iteration space for PCR.
*)

LOCAL INSTANCE Naturals

VARIABLE map

CONSTANTS InType,       \* Type of PCR input
          CtxIdType,
          IndexType,    \* Type of iteration space
          VarPType,     \* Type of producer variable
          VarCType,     \* Type of consumer variable
          VarRType,     \* Type of reducer output         
          NULL          \* Nothing
          
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
Iterator(i) == range(LowerBnd(in(i)), UpperBnd(in(i)), Step)

Bound(i) == i_p(i) \in Iterator(i)    

CDone(i, j) == \A k \in Iterator(i)\{j} : Read(v_c(i), k)                  

\* Quit action: if iteration space is empty then PCR inmediately terminate        
Quit(i) == /\ Iterator(i) = {} 
           /\ map' = [map EXCEPT ![i].ste = "END"]     

=============================================================================
\* Modification History
\* Last modified Sun Sep 20 22:25:10 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
