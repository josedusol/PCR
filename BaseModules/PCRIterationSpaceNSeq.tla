----------------------- MODULE PCRIterationSpaceNSeq ------------------------

(*
   Iteration space for PCR with sequential producer and N consumers.
*)

LOCAL INSTANCE Naturals

VARIABLES cm, im

CONSTANTS InType,
          CtxIdType,
          IndexType,
          VarPType,
          VarCType,
          VarRType,
          Undef
          
LOCAL INSTANCE PCRBaseN

CONSTANTS lowerBnd(_),
          upperBnd(_),
          step(_)

ASSUME Undef \notin IndexType

range(start, end, stp(_)) ==
  LET f[i \in Nat] == 
        IF i <= end
        THEN {i} \union f[stp(i)]
        ELSE {}    
  IN  f[start]  

i_p(I)   == im[I]
IndexMap == [CtxIdType -> IndexType \union {Undef}]

p_last(I)   == v_p(I)[upperBnd(in(I))].v
c_last(k,I) == v_c(k,I)[upperBnd(in(I))].v

\* Any PCR have an iteration space: a set of indexes  
iterator(I) == range(lowerBnd(in(I)), upperBnd(in(I)), step)   

cDone(I, i) == \A j \in iterator(I)\{i} : /\ written(v_c(cLen, I), j) 
                                          /\ read(v_c(cLen, I), j)

\* Start action         
Start(I) == cm' = [cm EXCEPT ![I].ste = "RUN"] 

\* Terminate if iteration space is empty      
Quit(I) == /\ iterator(I) = {} 
           /\ cm' = [cm EXCEPT ![I].ste = "END"]   

=============================================================================
\* Modification History
\* Last modified Fri Nov 20 23:12:26 UYT 2020 by josedu
\* Created Wed Oct 21 14:41:43 UYT 2020 by josedu
