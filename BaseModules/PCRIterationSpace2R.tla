------------------------- MODULE PCRIterationSpace2R ------------------------

(*
   Iteration space for PCR with two consumers.
   
   This is an experimental alternative version where the reducer is also
   a stream variable.   
*)

LOCAL INSTANCE Naturals

VARIABLE cm

CONSTANTS InType,
          CtxIdType,
          IndexType,
          VarPType,
          VarC1Type,
          VarC2Type,
          VarRType,
          Undef
          
LOCAL INSTANCE PCRBase2R

CONSTANTS lowerBnd(_),
          upperBnd(_),
          step(_)

range(start, end, stp(_)) ==
  LET f[i \in Nat] == 
        IF i <= end
        THEN {i} \union f[stp(i)]
        ELSE {}    
  IN  f[start]  

p_last(I)  == v_p(I)[upperBnd(in(I))].v
c1_last(I) == v_c1(I)[upperBnd(in(I))].v
c2_last(I) == v_c2(I)[upperBnd(in(I))].v
r_last(I)  == v_r(I)[upperBnd(in(I))].v

\* Any PCR have an iteration space: a set of indexes  
iterator(I) == range(lowerBnd(in(I)), upperBnd(in(I)), step)

\* Reduction done 
rDone(I, i) == \A j \in iterator(I)\{i} : ~ pending(I, j)

\* Start action         
Start(I) == cm' = [cm EXCEPT ![I].ste = "RUN"] 

\* Terminate if iteration space is empty      
Quit(I) == /\ iterator(I) = {} 
           /\ cm' = [cm EXCEPT ![I].ste = "END"]     

=============================================================================
\* Modification History
\* Last modified Sat Nov 21 16:52:19 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
