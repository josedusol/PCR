----------------------- MODULE AbelianMonoidBigOpThms -----------------------

(* 
  This module states theorems for module AbelianMonoidBigOp.
  
  See proofs in module AbelianMonoidBigOpThms_proofs.
*) 

EXTENDS AbelianMonoidBigOp, MonoidBigOpThms

LOCAL INSTANCE Naturals

-----------------------------------------------------------------------------
                                                   
(* 
  Distributivity (aka linearity).

  `^\displaystyle \quad 
      \BigOp{m}{n}{f(i)} \ \otimes \ \BigOp{m}{n}{g(i)} 
        \ = \ \BigOp{m}{n}{(f(i) \otimes g(i))}^'   
*)
THEOREM Linearity == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,    
         NEW f(_), \A x \in m..n : f(x) \in D,
         NEW g(_), \A x \in m..n : g(x) \in D,
         m <= n
  PROVE BigOp(m,n,f) (\X) BigOp(m,n,g) = BigOp(m,n,LAMBDA i : f(i) (\X) g(i)) 

(* 
  Skip index outside operation interval has no effect. 
  That is, if `^$j \notin m..n$^' then:
  
  `^\displaystyle \quad \BigOpP{m}{n}{i\neq j}{f(i)} \ = \ \BigOp{m}{n}{f(i)}^'   
*) 
THEOREM SkipOutOfBounds == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW f(_), \A x \in m..n : f(x) \in D,
         NEW j, j \notin m..n
  PROVE BigOpP(m,n,LAMBDA i : i # j, f) = BigOp(m,n,f)

(* 
  For any `^$j \in m..n$^', the j-indexed term can be extracted.
  
  `^\displaystyle \quad 
      \BigOp{m}{n}{f(i)} \ = \ \BigOpP{m}{n}{i\neq j}{f(i)} \ \otimes \ f(j)^'   
*)   
THEOREM SplitRandom == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW f(_), \A i \in m..n : f(i) \in D,
         NEW j \in m..n,
         m <= n
  PROVE BigOp(m,n,f) = BigOpP(m,n,LAMBDA i : i # j, f) (\X) f(j)  

(*   
  For any `^$j \in m..n$^' and predicate `^$P$^' for which `^$P(j)$^' 
  holds, the j-indexed term can be extracted.

  `^\displaystyle \quad 
      \BigOpP{m}{n}{P(i)}{f(i)}
        \ = \ \BigOpP{m}{n}{P(i) \land i \neq j}{f(i)} \ \otimes \ f(j)^'           
*)   
COROLLARY SplitRandomP == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_), \A i \in m..n : P(i) \in BOOLEAN,
         NEW f(_), \A i \in {k \in m..n : P(k)} : f(i) \in D,        
         NEW j \in m..n, P(j),
         m <= n
  PROVE BigOpP(m,n,P,f) = BigOpP(m,n,LAMBDA i : P(i) /\ i # j, f) (\X) f(j)

=============================================================================
\* Modification History
\* Last modified Wed Aug 04 17:00:51 UYT 2021 by josedu
\* Last modified Mon Jun 28 21:36:53 GMT-03:00 2021 by JosEdu
\* Created Fri Jan 22 21:50:30 UYT 2021 by josedu
