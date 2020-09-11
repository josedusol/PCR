------------------------------ MODULE Theorems ------------------------------

EXTENDS MainPCRCountWords2, TLAPS

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

THEOREM Thm4_Refinement == Spec => PCRCountWords1!Spec
  PROOF OMITTED

=============================================================================
\* Modification History
\* Last modified Thu Sep 10 02:49:31 UYT 2020 by josedu
\* Created Wed Sep 09 19:22:17 UYT 2020 by josedu
