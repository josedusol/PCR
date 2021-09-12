-------------------------- MODULE MonoidBigOpThms --------------------------

(* 
  This module states theorems for module MonoidBigOp.
  
  See proofs in module MonoidBigOpThms_proofs.
*) 

EXTENDS MonoidBigOp

LOCAL INSTANCE NaturalsInduction

----------------------------------------------------------------------------
  
(* 
  The following theorems asserts that our definition of bigOp is well defined, 
  that is, there exists a function matching the recursive definition.
*)

LEMMA bigOpDefConclusion ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW f(_)
  PROVE FiniteNatInductiveDefConclusion(bigOp(m,n,f), f(m), LAMBDA v,i : f(i) (\X) v, m, n) 

THEOREM bigOpDef ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW f(_),  
         NEW i \in m..n
  PROVE bigOp(m,n,f)[i] = IF i = m THEN f(m) ELSE bigOp(m,n,f)[i-1] (\X) f(i) 

(*
  The bigOp function type.
  
  `^\displaystyle\quad 
      \bigOp{m}{n}{f} \ : \ m..n \to D^'
*)  
THEOREM bigOpType == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,  
         NEW f(_), \A x \in m..n : f(x) \in D,
         m <= n
  PROVE bigOp(m,n,f) \in [m..n -> D]

(* 
  The base case for bigOp function:

  `^\displaystyle\quad
      \bigOp{m}{n}{f}\,[i] = f(m) \ \ \textrm{when} \ \ \ i = m^'   
*) 
LEMMA bigOpBaseCase ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat, 
         NEW i \in m..n, i = m,
         NEW f(_)
  PROVE bigOp(m,n,f)[i] = f(m)

(* 
  The recursive step for bigOp function:

  `^\displaystyle\quad 
      \bigOp{m}{n}{f}\,[i] 
         \ = \ \bigOp{m}{n}{f}\,[i-1] \, \oplus \, f(i)
         \ \ \ \textrm{when} \ \ \ i \neq m^'   
*)   
LEMMA bigOpRecStep ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat, 
         NEW i \in m..n, i # m,
         NEW f(_)
  PROVE bigOp(m,n,f)[i] = bigOp(m,n,f)[i-1] (\X) f(i) 

(*
  The BigOp result type.
  
  `^\displaystyle\quad
      \BigOp{m}{n}{f(i)} \in D^'
*)
THEOREM BigOpType == 
 ASSUME NEW m \in Nat,
        NEW n \in Nat,
        NEW f(_), \A x \in m..n : f(x) \in D
  PROVE BigOp(m,n,f) \in D 

----------------------------------------------------------------------------

(* 
  The (assumed) monoid laws for binary operator `^$\otimes$^'. 
*) 

PROPOSITION OpClosure == 
  \A x, y \in D : x (\X) y \in D

PROPOSITION OpAssociativity == 
  \A x, y, z \in D : (x (\X) y) (\X) z = x (\X) (y (\X) z)

PROPOSITION OpIdentity == 
  \E e \in D : \A x \in D : /\ e = Id 
                            /\ x  (\X) Id = x 
                            /\ Id (\X) x = x

THEOREM OpUniqueIdentity == 
  ASSUME NEW e1, NEW e2,
         \A x : x (\X) e1 = x /\ e1 (\X) x = x,
         \A x : x (\X) e2 = x /\ e2 (\X) x = x
  PROVE  e1 = e2

PROPOSITION OpIdentityLeft == 
  \A x \in D : Id (\X) x = x
  BY OpIdentity    
  
PROPOSITION OpIdentityRight == 
  \A x \in D : x (\X) Id = x
  BY OpIdentity 

----------------------------------------------------------------------------

(* 
  To evaluate the bigOp function on `^$m..n$^' starting from any `^$i \in m..n$^' 
  is the same as evaluating on subinterval `^$m..i$^' starting from `^$i$^'. That is:
  
  `^\displaystyle\quad
      \bigOp{m}{n}{f}\,[i] \ = \ \bigOp{m}{i}{f}\,[i] ^'
  
  This fact is used in some proofs. For example, when `^$i \neq m$^'
  in the recursive step we have: 
  
  `^\displaystyle\quad 
      \bigOp{m}{n}{f}\,[i] \ = \ \bigOp{m}{n}{f}\,[i-1]   \, \otimes \,f(i)
                           \ = \ \bigOp{m}{n-1}{f}\,[i-1] \, \otimes \,f(i)^' 
*)
THEOREM BasicNotationalEq == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW l \in m..n,
         NEW f(_), \A x \in m..n : f(x) \in D,
         m <= n
  PROVE  bigOp(m,n,f)[l] = bigOp(m,l,f)[l]

(*
  BigOp over constant identity.
  
  `^\displaystyle\quad
      \BigOp{m}{n}{Id} = Id^'
*)
THEOREM OpIdentityExt == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat
  PROVE BigOp(m,n,LAMBDA i : Id) = Id

(* 
  If `^$f(i) = g(i)$^' for all `^$i \in m..n$^' then:

  `^\displaystyle\quad
      \BigOp{m}{n}{f(i)} \ = \ \BigOp{m}{n}{g(i)}^'   
*) 
THEOREM FunctionEq == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW f(_), \A i \in m..n : f(i) \in D,
         NEW g(_), \A i \in m..n : g(i) \in D,
         \A i \in m..n : f(i) = g(i)
  PROVE BigOp(m,n,f) = BigOp(m,n,g)
  
(* 
  Operation over unitary interval is trivial.

  `^\displaystyle\quad
      \BigOp{n}{n}{f(i)} \ = \ f(n)^'   
*)
THEOREM UnitInterval == 
  ASSUME NEW n \in Nat, 
         NEW f(_)
  PROVE BigOp(n,n,f) = f(n)                                                        

(* 
  For any `^$k \in m..n$^', operation can be split at `^$k$^'.

  `^\displaystyle\quad 
      \BigOp{m}{n}{f(i)}
        \ = \ \BigOp{m}{k}{f(i)} \ \otimes \ \BigOp{k+1}{n}{f(i)}^'               
*)
THEOREM SplitUp == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,    
         NEW f(_), \A x \in m..n : f(x) \in D,
         NEW k \in m..n,
         m <= n
  PROVE BigOp(m,n,f) = BigOp(m,k,f) (\X) BigOp(k+1,n,f)

(* 
  For any `^$k \in m..n$^', operation can be split at `^$k-1$^'.

  `^\displaystyle\quad 
      \BigOp{m}{n}{f(i)}
        \ = \ \BigOp{m}{k-1}{f(i)} \ \otimes \ \BigOp{k}{n}{f(i)}^'   
*)  
THEOREM SplitDown == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,    
         NEW f(_), \A x \in m..n : f(x) \in D,
         NEW k \in m+1..n,
         m <= n
  PROVE BigOp(m,n,f) = BigOp(m,k-1,f) (\X) BigOp(k,n,f)

(* 
  Extraction of the m-indexed (first) term.

  `^\displaystyle\quad 
      \BigOp{m}{n}{f(i)} \ = \ f(m) \ \otimes \BigOp{m+1}{n}{f(i)}^'   
*)  
THEOREM SplitFirst == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW f(_), \A x \in m..n : f(x) \in D,
         m <= n
  PROVE BigOp(m,n,f) = f(m) (\X) BigOp(m+1,n,f)
  
(* 
  Extraction of the n-indexed (last) term.

  `^\displaystyle\quad 
      \BigOp{m}{n}{f(i)} \ = \ \BigOp{m}{n-1}{f(i)} \ \otimes \ f(n)^'   
*)  
THEOREM SplitLast == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW f(_), \A x \in m..n : f(x) \in D,
         m <= n
  PROVE BigOp(m,n,f) = BigOp(m,n-1,f) (\X) f(n)

----------------------------------------------------------------------------

(* 
  When `^$m > n$^', and thus inverval `^$m..n$^' is empty, it is assumed the 
  result is the monoid identity `^$Id$^'.
*)
COROLLARY EmptyIntvAssumpP ==  
  ASSUME NEW m \in Int,
         NEW n \in Int,
         NEW P(_),
         NEW f(_),
         n < m
  PROVE  BigOpP(m,n,P,f) = Id

(*
  The BigOpP result type.
  
  `^\displaystyle\quad
      \BigOpP{m}{n}{P(i)}{f(i)} \in D^'
*)
COROLLARY BigOpPType == 
 ASSUME NEW m \in Nat,
        NEW n \in Nat,
        NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
        NEW f(_), \A x \in {i \in m..n : P(i)} : f(x) \in D
  PROVE BigOpP(m,n,P,f) \in D

(*
  BigOpP over constant identity.
  
  `^\displaystyle\quad
      \BigOpP{m}{n}{P(i)}{Id} = Id^'
*)
COROLLARY OpIdentityExtP == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i) \in BOOLEAN
  PROVE BigOpP(m,n,P,LAMBDA i : Id) = Id

(* 
  If `^$f(i) = g(i)$^' for all `^$i \in m..n$^' then:

  `^\displaystyle\quad
      \BigOpP{m}{n}{P(i)}{f(i)} \ = \ \BigOpP{m}{n}{P(i)}{g(i)}^'   
*) 
COROLLARY FunctionEqP == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
         NEW f(_), \A i \in {j \in m..n : P(j)} : f(i) \in D,
         NEW g(_), \A i \in {j \in m..n : P(j)} : g(i) \in D,
         \A i \in {j \in m..n : P(j)} : f(i) = g(i)
  PROVE BigOpP(m,n,P,f) = BigOpP(m,n,P,g)

(*
  For always false predicate `^$P$^' the result is identity.
  
  `^\displaystyle\quad
      \BigOpP{m}{n}{P(i)}{f(i)} = Id^'
*)
COROLLARY FalsePredicate == 
 ASSUME NEW m \in Nat,
        NEW n \in Nat,
        NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
        NEW f(_), \A x \in {i \in m..n : P(i)} : f(x) \in D,
        \A i \in m..n : ~ P(i)
  PROVE BigOpP(m,n,P,f) = Id
 
(*
  For always true predicate `^$P$^', collapse to basic definition.
  
  `^\displaystyle\quad 
      \BigOpP{m}{n}{P(i)}{f(i)} = \BigOp{m}{n}{f(i)}^'
*)
COROLLARY TruePredicate == 
 ASSUME NEW m \in Nat,
        NEW n \in Nat,
        NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
        NEW f(_), \A x \in {i \in m..n : P(i)} : f(x) \in D,
        \A i \in m..n : P(i)
  PROVE BigOpP(m,n,P,f) = BigOp(m,n,f) 
  
(* 
  If `^$P(i) \equiv Q(i)$^' for all `^$i \in m..n$^' then:

  `^\displaystyle\quad 
      \BigOpP{m}{n}{P(i)}{f(i)} \ = \ \BigOpP{m}{n}{Q(i)}{f(i)}^'   
*) 
COROLLARY PredicateEq == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
         NEW Q(_), \A i \in m..n : Q(i) \in BOOLEAN,
         NEW f(_), \A i \in {j \in m..n : P(j) /\ Q(j)} : f(i) \in D,
         \A i \in m..n : P(i) <=> Q(i)
  PROVE BigOpP(m,n,P,f) = BigOpP(m,n,Q,f)
  
(* 
  Operation over unitary interval is trivial.

  `^\displaystyle\quad 
      \BigOpP{n}{n}{P(i)}{f(i)} \ = \ (P(n) \to f(n),\ Id)^'   
*)
COROLLARY UnitIntervalP == 
  ASSUME NEW n \in Nat, 
         NEW P(_),
         NEW f(_)
  PROVE BigOpP(n,n,P,f) = IF P(n) THEN f(n) ELSE Id  
  
(* 
  For any `^$k \in m..n$^', operation can be split at `^$k$^'.

  `^\displaystyle\quad 
      \BigOpP{m}{n}{P(i)}{f(i)}  
        \ = \ \BigOpP{m}{k}{P(i)}{f(i)} \ \otimes \ \BigOpP{k+1}{n}{P(i)}{f(i)}^'   
*)
COROLLARY SplitUpP == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,    
         NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
         NEW f(_), \A x \in {i \in m..n : P(i)} : f(x) \in D,
         NEW k \in m..n,
         m <= n
  PROVE BigOpP(m,n,P,f) = BigOpP(m,k,P,f) (\X) BigOpP(k+1,n,P,f)

(* 
  For any `^$k \in m..n$^', operation can be split at `^$k-1$^'.

  `^\displaystyle\quad 
      \BigOpP{m}{n}{P(i)}{f(i)}  
        \ = \ \BigOpP{m}{k-1}{P(i)}{f(i)} \ \otimes \ \BigOpP{k}{n}{P(i)}{f(i)}^'    
*)  
COROLLARY SplitDownP == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,    
         NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
         NEW f(_), \A x \in {i \in m..n : P(i)} : f(x) \in D,
         NEW k \in m+1..n,
         m <= n
  PROVE BigOpP(m,n,P,f) = BigOpP(m,k-1,P,f) (\X) BigOpP(k,n,P,f)     

(* 
  Extraction of the m-indexed (first) term.

  `^\displaystyle\quad 
      \BigOpP{m}{n}{P(i)}{f(i)}
        \ = \ (P(m) \to f(m),\ Id) \ \otimes \ \BigOpP{m+1}{n}{P(i)}{f(i)}^'   
*)  
COROLLARY SplitFirstP == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
         NEW f(_), \A x \in {i \in m..n : P(i)} : f(x) \in D,
         m <= n
  PROVE BigOpP(m,n,P,f) = (IF P(m) THEN f(m) ELSE Id) (\X) BigOpP(m+1,n,P,f)

(* 
  Extraction of the n-indexed (last) term.

  `^\displaystyle\quad 
      \BigOpP{m}{n}{P(i)}{f(i)}
         \ = \ \BigOpP{m}{n-1}{P(i)}{f(i)} \ \otimes \ (P(n) \to f(n),\ Id)^'   
*)  
COROLLARY SplitLastP == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
         NEW f(_), \A x \in {i \in m..n : P(i)} : f(x) \in D,
         m <= n
  PROVE BigOpP(m,n,P,f) = BigOpP(m,n-1,P,f) (\X) IF P(n) THEN f(n) ELSE Id

============================================================================
\* Modification History
\* Last modified Mon Aug 16 15:13:36 UYT 2021 by josedu
\* Last modified Mon Jun 28 21:35:24 GMT-03:00 2021 by JosEdu
\* Created Fri Jan 22 21:50:30 UYT 2021 by josedu
