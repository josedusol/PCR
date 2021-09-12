--------------------------- MODULE ArithUtilsThms ---------------------------

(* 
  This module states properties for operators defined in ArithUtils.
  
  See proofs in ArithUtilsThms_proofs.
*)

EXTENDS ArithUtils, FiniteSets

LOCAL INSTANCE Naturals

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

(* 
  
*)
THEOREM MinOfNat ==
  ASSUME NEW S \in SUBSET Nat, 
         S # {}
  PROVE  /\ Min(S) \in S
         /\ \A y \in S : Min(S) <= y

(* 
  
*)
THEOREM MaxOfNat ==
  ASSUME NEW S \in SUBSET Nat, 
         S # {}, 
         IsFiniteSet(S)
  PROVE  /\ Max(S) \in S
         /\ \A y \in S : y <= Max(S)

(* 
  
*)
THEOREM MinIsIntervalLowerBnd ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i)
  PROVE  Min({ i \in m..n : P(i)}) = m

(* 
  
*)
THEOREM MaxIsIntervalUpperBnd ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i)
  PROVE  Max({ i \in m..n : P(i)}) = n

(* 
  The fibonacci function definition.
*)
THEOREM fibonacciDef ==
  ASSUME NEW n \in Nat
  PROVE  fibonacci[n] = IF n <= 2 THEN 1 ELSE fibonacci[n-1] + fibonacci[n-2] 

(*
  The fibonacci function type.
*)  
THEOREM fibonacciType == 
  ASSUME NEW n \in Nat          
  PROVE  fibonacci \in [Nat -> Nat]

=============================================================================
\* Modification History
\* Last modified Mon Jul 05 18:18:54 GMT-03:00 2021 by JosEdu
\* Last modified Mon Feb 01 16:41:29 UYT 2021 by josedu
\* Created Sat Jan 23 00:50:36 UYT 2021 by josedu
