----------------------- MODULE ArithUtilsThms_proofs -----------------------

(* 
  This module proves properties for operators defined in ArithUtils.
*)

EXTENDS ArithUtils

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetTheorems 
LOCAL INSTANCE NaturalsInduction
LOCAL INSTANCE TLAPS

(* 
  Induction principle for intervals of natural numbers.
*)
THEOREM IntervalNatInduction ==
  ASSUME NEW m \in Nat, 
         NEW n \in Nat,
         NEW P(_),
         P(m),
         \A i \in (m+1)..n : P(i-1) => P(i)
  PROVE  \A i \in m..n : P(i)
<1> DEFINE Q(i) == i \in m..n => P(i)
<1> SUFFICES \A i \in Nat : Q(i)   BY m..n \subseteq Nat
<1>1. Q(0)                         OBVIOUS
<1>2. ASSUME NEW i \in Nat, Q(i)
      PROVE  Q(i+1)                BY <1>2
<1>. QED
  BY <1>1, <1>2, NatInduction, Isa

(* 
  Strong (aka complete/course-of-values) induction principle for 
  intervals of natural numbers.
*)
THEOREM IntervalGeneralNatInduction ==
  ASSUME NEW m \in Nat, 
         NEW n \in Nat,
         NEW P(_),
         \A i \in m..n : (\A j \in m..(i-1) : P(j)) => P(i)
  PROVE  \A i \in m..n : P(i)
<1> DEFINE Q(k) == \A i \in m..k-1 : P(i)
<1>1. Q(m)                                OBVIOUS
<1>2. \A k \in (m+1)..n : Q(k-1) => Q(k)  OBVIOUS
<1>3. \A k \in m..n : Q(k)                BY <1>1, <1>2, IntervalNatInduction, Isa
<1>4. QED 
  BY <1>3

(* 
  
*)
THEOREM MinOfNat ==
  ASSUME NEW S \in SUBSET Nat, 
         S # {}
  PROVE  /\ Min(S) \in S
         /\ \A y \in S : Min(S) <= y
<1>0. SUFFICES ASSUME ~ \E x \in S : \A y \in S : x <= y 
               PROVE  FALSE
  BY DEF Min   
<1>1. \A x \in S : \E y \in S : x > y  BY  <1>0
<1>2. S = {}  
  <2> DEFINE P(n) == n \notin S
  <2>1. ASSUME NEW n \in Nat, 
               \A m \in 0..(n-1) : P(m)  \* HI
        PROVE  P(n)
    <3>0. SUFFICES ASSUME ~ P(n)
                  PROVE  FALSE
      OBVIOUS   
    <3>1. n \in S                        BY <3>0
    <3>2. \E m \in S : n > m             BY <1>1, <3>1   
    <3>3. \A m \in 0..(n-1) : m \notin S BY <2>1 
    <3>4. FALSE                          BY <3>2, <3>3     
    <3> QED 
      BY <3>4   
  <2> HIDE DEF P      
  <2>2. \A n \in Nat : P(n)
    BY <2>1, GeneralNatInduction      
  <2> QED  
   BY <2>2 DEF P       
<1> QED
  BY <1>2

(* 
  
*)
THEOREM MaxOfNat ==
  ASSUME NEW S \in SUBSET Nat, 
         S # {}, 
         IsFiniteSet(S)
  PROVE  /\ Max(S) \in S
         /\ \A y \in S : y <= Max(S)
<1> DEFINE P(T) == T \in SUBSET Nat /\ T # {} => \E x \in T : \A y \in T : y <= x
<1>1. P({})
  OBVIOUS
<1>2. ASSUME NEW T, NEW x, P(T), x \notin T
      PROVE  P(T \cup {x})
  <2> HAVE T \cup {x} \in SUBSET Nat
  <2>1. CASE \A y \in T : y <= x
    BY <2>1, Isa
  <2>2. CASE \E y \in T : ~(y <= x)
    <3> T # {}
      BY <2>2
    <3>1. PICK y \in T : \A z \in T : z <= y
      BY <1>2
    <3>2. x <= y
      BY <2>2, <3>1
    <3> QED  BY <3>1, <3>2
  <2> QED  BY <2>1, <2>2
<1> HIDE DEF P
<1>3. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1> QED 
  BY <1>3, Zenon DEF Max, P

(* 
  
*)
THEOREM MinIsIntervalLowerBnd ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i)
  PROVE  Min({ i \in m..n : P(i)}) = m
<1>1. { i \in m..n : P(i)} = { i : i \in m..n } OBVIOUS
<1>2. Min({ i : i \in m..n }) = m               BY DEF Min
<1> QED
  BY <1>1, <1>2 

(* 
  
*)               
THEOREM MaxIsIntervalUpperBnd ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i)
  PROVE  Max({ i \in m..n : P(i)}) = n
<1>1. { i \in m..n : P(i)} = { i : i \in m..n } OBVIOUS
<1>2. Max({ i : i \in m..n }) = n               BY DEF Max
<1> QED
  BY <1>1, <1>2
  
=============================================================================
\* Modification History
\* Last modified Mon Feb 01 16:42:11 UYT 2021 by josedu
\* Created Sat Jan 23 00:51:35 UYT 2021 by josedu
