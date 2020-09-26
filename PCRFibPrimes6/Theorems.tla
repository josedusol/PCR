------------------------------ MODULE Theorems ------------------------------

EXTENDS MainPCRFibPrimes6, TLAPS

THEOREM Thm1_TypeInv ==
  \A n \in InType1 : /\ N = n 
                     /\ Spec 
                     => []TypeInv
  PROOF OMITTED

THEOREM Thm2_Correctness == 
  \A n \in InType1 : /\ N = n 
                     /\ Spec 
                     => [](PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(n))
  PROOF OMITTED 

THEOREM Thm3_Termination == 
  \A n \in InType1 : /\ N = n 
                     /\ FairSpec 
                     => Termination
  PROOF OMITTED 

THEOREM Thm4_Refinement == Spec => PCRFibPrimes1!Spec
  PROOF OMITTED

=============================================================================
\* Modification History
\* Last modified Fri Sep 25 23:37:05 UYT 2020 by josedu
\* Created Wed Sep 09 00:33:06 UYT 2020 by josedu