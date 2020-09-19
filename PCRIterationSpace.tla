---------------------- MODULE PCRIterationSpace ----------------------

(*
   Main module for PCR MergeSort.
*)


EXTENDS Naturals

VARIABLE map

CONSTANTS IndexType,
          LowerBnd(_),
          UpperBnd(_),
          Step(_)

LOCAL OFF == 0
LOCAL RUN == 1
LOCAL END == 2

LOCAL in(i)  == map[i].in
LOCAL i_p(i) == map[i].i_p
LOCAL v_c(i) == map[i].v_c

\* Any PCR have an iteration space: a set of indexes
range(start, end, step(_)) ==
  LET F[i \in IndexType] == 
        IF i <= end
        THEN {i} \union F[step(i)]
        ELSE {}    
  IN  F[start]  
Iterator(i) == range(LowerBnd(in(i)), UpperBnd(in(i)), Step)
Bound(i)    == i_p(i) \in Iterator(i)    

LOCAL Read(var, j)    == var[j].r > 0      
CDone(i, j)     == \A k \in Iterator(i)\{j} : Read(v_c(i), k)                  
        

Quit(i) == /\ Iterator(i) = {} 
           /\ map' = [map EXCEPT ![i].ste = END]     


=============================================================================
\* Modification History
\* Last modified Sat Sep 19 01:04:17 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
