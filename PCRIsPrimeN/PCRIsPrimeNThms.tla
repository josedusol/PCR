--------------------------- MODULE PCRIsPrimeNThms --------------------------

VARIABLES N, cm1 

CONSTANT Undef

INSTANCE TLAPS
INSTANCE PCRIsPrimeNMain

USE DEF IndexType1, CtxIdType1, InType1, VarPType1, VarCType1, VarRType1
 
LEMMA Lem_IteratorType == Spec => []IteratorType 

LEMMA Lem_divisorsType == 
  ASSUME NEW x \in Nat,
         NEW p \in PCR1!VarP,
         NEW i \in Nat
  PROVE PCR1!divisors(x, p, i) \in Nat
   BY DEF PCR1!divisors 

LEMMA Lem_notDividesType == 
  ASSUME NEW x \in Nat,
         NEW p \in PCR1!VarP,
         NEW i \in Nat,
         p[i].v \in Nat
  PROVE PCR1!notDivides(x, p, i) \in BOOLEAN
  BY DEF PCR1!notDivides

LEMMA Lem_andType == 
  ASSUME NEW a \in BOOLEAN,
         NEW b \in BOOLEAN
  PROVE PCR1!and(a, b) \in BOOLEAN
  BY DEF PCR1!and

THEOREM Thm_TypeInv == Spec => []TypeInv
<1>1. Init => TypeInv
  <2> SUFFICES ASSUME Init
               PROVE  TypeInv
    OBVIOUS
  <2>1. N   \in InType1
  <2>2. cm1 \in PCR1!CtxMap
  <2> QED
    BY <2>1, <2>2 DEF TypeInv
<1>2. TypeInv /\ IteratorType /\ [Next]_vars => TypeInv'
  <2>0. SUFFICES ASSUME TypeInv,
                        IteratorType,
                        [Next]_vars
                 PROVE  TypeInv'
    OBVIOUS
  <2>1. CASE \E I \in Seq(Nat) : Next1(I)
    <3>0. SUFFICES ASSUME NEW I \in Seq(Nat),
                          Next1(I)
                   PROVE  TypeInv'
      BY <2>1 DEF Next1  
    <3>A. CASE /\ PCR1!state(I) = "OFF"
               /\ PCR1!Start(I) 
    <3>B. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!P(I)   
    <3>C. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!C(I)     
    <3>D. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!R(I)                        
    <3>E. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!Quit(I)                     
    <3> QED
      BY <3>0, <3>A, <3>B, <3>C, <3>D, <3>E DEF Next1, PCR1!Next
  <2>2. CASE Done
  <2>3. CASE UNCHANGED vars
    <3>1. /\ N'   \in InType1
          /\ cm1' \in PCR1!CtxMap    BY <2>0, <2>3 DEF TypeInv, vars   
    <3> QED 
      BY <3>1 DEF TypeInv
  <2> QED
    BY <2>0, <2>1, <2>2, <2>3 DEF Next
<1> QED 
  BY <1>1, <1>2, PTL, Lem_IteratorType DEF Spec 

THEOREM Thm_Correctness == 
  \A n \in InType1 : /\ N = n 
                     /\ Spec 
                     => [](PCR1!finished(<< >>) => PCR1!out(<< >>) = Solution(n))
  PROOF OMITTED                     

THEOREM Thm_Termination == 
  \A n \in InType1 : /\ N = n 
                     /\ FairSpec 
                     => Termination
  PROOF OMITTED 

=============================================================================
\* Modification History
\* Last modified Wed Nov 18 17:47:28 UYT 2020 by josedu
\* Created Wed Sep 09 00:30:16 UYT 2020 by josedu