------------------------- MODULE PCRIterationSpaceT -------------------------

(*
   Iteration space for PCR.
   
   This is an experimental alternative version where we replace the Undef
   and partial function concepts by explicitly defining and mantaining 
   function domains.   
*)

LOCAL INSTANCE Naturals

VARIABLES cm, cmDom, vpDom, vcDom

CONSTANTS InType,
          CtxIdType,
          IndexType,
          VarPType,
          VarCType,
          VarRType
          
LOCAL INSTANCE PCRBaseT

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

cDone(I, i) == \A j \in iterator(I)\{i} : /\ written(v_c(I), j) 
                                          /\ read(v_c(I), j)

\* Start action         
Start(I) == /\ cm' = [cm EXCEPT ![I].ste = "RUN"]
            /\ UNCHANGED <<cmDom, vpDom, vcDom>> 

\* Terminate if iteration space is empty      
Quit(I) == /\ iterator(I) = {} 
           /\ cm' = [cm EXCEPT ![I].ste = "END"]   
           /\ UNCHANGED <<cmDom, vpDom, vcDom>>  

-----------------------------------------------------------------------------

LEMMA Lem_RangeType == 
  ASSUME NEW start \in Nat,
         NEW end \in Nat,
         NEW stp(_)
  PROVE range(start, end, stp) \in SUBSET Nat
  OMITTED

LEMMA Lem_Range == 
  ASSUME NEW start \in Nat,
         NEW end \in Nat,
         NEW stp(_)
  PROVE range(start, end, stp) = { n \in Nat : \A i \in start..end : 
                                                  i # start
                                                  => \E j \in start..end : j # i /\ j = stp(i)  }
  OMITTED

=============================================================================
\* Modification History
\* Last modified Fri Nov 06 14:25:27 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed