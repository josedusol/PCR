------------------------------ MODULE Theorems ------------------------------

EXTENDS MainPCRNQueensAll, TLAPS

THEOREM Thm1_TypeInv == 
  \A l \in InType1 : /\ L = l  
                     /\ Spec 
                     => []TypeInv
  PROOF OMITTED 

THEOREM Thm2_Correctness == 
  \A l \in InType1 : /\ L = l 
                     /\ Spec 
                     => [](PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(l))
  PROOF OMITTED 

THEOREM Thm3_Termination == 
  \A l \in InType1 : /\ L = l 
                     /\ FairSpec 
                     => Termination
  PROOF OMITTED 

=============================================================================
\* Modification History
\* Last modified Sun Sep 13 16:41:06 UYT 2020 by josedu
\* Created Wed Sep 09 16:41:05 UYT 2020 by josedu
