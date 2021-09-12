-------------------------- MODULE AbstractAlgebra --------------------------

(* 
  This module formally defines some basic algebraic structures. 
*) 

EXTENDS TLAPS

----------------------------------------------------------------------------

(*
  A Magma consists of a set `^$D$^' equipped with a single binary 
  operation `^$\otimes$^' that is closed on `^$D$^'.
*)
Magma(D, _(\X)_) == 
  \A x, y \in D : x (\X) y \in D

(*
  A SemiGroup is a Magma where operation `^$\otimes : D \times D \to D$^'
  satisfies Associativity.
*)
SemiGroup(D, _(\X)_) == 
  /\ Magma(D, (\X))
  /\ \A x, y, z \in D : (x (\X) y) (\X) z = x (\X) (y (\X) z)

(*
  A Monoid is a SemiGroup with identity element for 
  operation `^$\otimes : D \times D \to D$^'.
*)                      
Monoid(D, c, _(\X)_) ==
  /\ SemiGroup(D, (\X))
  /\ \E e \in D : \A x \in D : /\ e = c
                               /\ x (\X) e = x 
                               /\ e (\X) x = x

Monoid2(D, _(\X)_) == 
  /\ SemiGroup(D, (\X))
  /\ \E e \in D : \A x \in D : /\ x (\X) e = x 
                               /\ e (\X) x = x

(*
  An Abelian Monoid is a Monoid where operation 
  `^$\otimes : D \times D \to D$^' satisfies Commutativity.
*)                                                   
AbelianMonoid(D, c, _(\X)_) ==
  /\ Monoid(D, c, (\X))
  /\ \A x, y \in D : x (\X) y = y (\X) x
  
AbelianMonoid2(D, _(\X)_) == 
  /\ Monoid2(D, (\X))
  /\ \A x, y \in D : x (\X) y = y (\X) x  

----------------------------------------------------------------------------

(* 
  The identity element in a Monoid is unique.
*) 
THEOREM MonoidUniqueIdentity == 
  ASSUME NEW D, NEW _(\X)_,
         Monoid2(D, (\X)),
         NEW e1, NEW e2,
         \A x : x (\X) e1 = x /\ e1 (\X) x = x,
         \A x : x (\X) e2 = x /\ e2 (\X) x = x
  PROVE  e1 = e2
  BY Z3 DEF Monoid2

============================================================================
\* Modification History
\* Last modified Thu Sep 09 01:47:38 UYT 2021 by josedu
\* Created Tue Jan 05 21:31:32 UYT 2021 by josedu
