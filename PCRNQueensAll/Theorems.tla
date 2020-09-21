------------------------------ MODULE Theorems ------------------------------

EXTENDS MainPCRNQueensAll, TLAPS

THEOREM Thm1_TypeInv == 
  \A b \in InType1 : /\ B = b  
                     /\ Spec 
                     => []TypeInv
  PROOF OMITTED 

THEOREM Thm2_Correctness == 
  \A b \in InType1 : /\ B = b 
                     /\ Spec 
                     => [](PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(b))
  PROOF OMITTED 

THEOREM Thm3_Termination == 
  \A b \in InType1 : /\ B = b 
                     /\ FairSpec 
                     => Termination
  PROOF OMITTED 

=============================================================================
\* Modification History
\* Last modified Sun Sep 20 20:00:59 UYT 2020 by josedu
\* Created Wed Sep 09 16:41:05 UYT 2020 by josedu
