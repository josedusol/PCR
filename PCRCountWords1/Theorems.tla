------------------------------ MODULE Theorems ------------------------------

EXTENDS MainPCRCountWords1

THEOREM Thm1_TypeInv == 
  \A <<t,w>> \in InType1 : /\ T = t 
                           /\ W = w 
                           /\ Spec 
                           => []TypeInv
  PROOF OMITTED 

THEOREM Thm2_Correctness == 
  \A <<t,w>> \in InType1 : /\ T = t 
                           /\ W = w 
                           /\ Spec 
                           => [](PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(t,w))
  PROOF OMITTED 

THEOREM Thm3_Termination == 
  \A <<t,w>> \in InType1 : /\ T = t 
                           /\ W = w 
                           /\ FairSpec 
                           => Termination
  PROOF OMITTED 

=============================================================================
\* Modification History
\* Last modified Wed Sep 09 16:41:56 UYT 2020 by josedu
\* Created Wed Sep 09 16:41:05 UYT 2020 by josedu
