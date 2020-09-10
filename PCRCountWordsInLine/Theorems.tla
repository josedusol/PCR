------------------------------ MODULE Theorems ------------------------------

EXTENDS MainPCRCountWordsInLine

THEOREM Thm1_TypeInv == 
  \A <<l,w>> \in InType1 : /\ L = l 
                           /\ W = w 
                           /\ Spec 
                           => []TypeInv
  PROOF OMITTED 

THEOREM Thm2_Correctness == 
  \A <<l,w>> \in InType1 : /\ L = l 
                           /\ W = w 
                           /\ Spec 
                           => [](PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(l,w))
  PROOF OMITTED 

THEOREM Thm3_Termination == 
  \A <<l,w>> \in InType1 : /\ L = l 
                           /\ W = w 
                           /\ FairSpec 
                           => Termination
  PROOF OMITTED 

=============================================================================
\* Modification History
\* Last modified Wed Sep 09 18:46:23 UYT 2020 by josedu
\* Created Wed Sep 09 18:45:54 UYT 2020 by josedu
