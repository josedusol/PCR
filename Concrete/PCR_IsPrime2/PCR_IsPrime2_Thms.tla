------------------------- MODULE PCR_IsPrime2_Thms -------------------------

EXTENDS PCR_IsPrime2, TLAPS

THEOREM \A x \in Nat : A(x) = IsPrime(x)
<1>1. SUFFICES ASSUME NEW x \in Nat
               PROVE A(x) = IsPrime(x)
  OBVIOUS               
<1> QED               


=============================================================================
\* Modification History
\* Last modified Thu Nov 18 19:40:43 UYT 2021 by josedu
\* Created Thu Nov 18 19:27:44 UYT 2021 by josedu
