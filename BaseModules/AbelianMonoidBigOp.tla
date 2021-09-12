------------------------- MODULE AbelianMonoidBigOp -------------------------

(* 
  Let `^$(D, Id, \otimes)$^' be an Abelian monoid structure. This module
  defines the extension of binary operation `^$\otimes$^' over 
  finite intervals.
 
  As order does not matter, definition from module MonoidBigOp is reused
  and commutativity is postulated as an additional assumption.
  
  See relevant theorems in module AbelianMonoidBigOpThms.
*) 

EXTENDS AbstractAlgebra, MonoidBigOp

AXIOM OpCommutativity == \A x, y \in D : x (\X) y = y (\X) x

=============================================================================
\* Modification History
\* Last modified Fri Jul 30 00:36:18 UYT 2021 by josedu
\* Last modified Mon Jun 28 21:36:31 GMT-03:00 2021 by JosEdu
\* Created Tue Jan 05 21:31:32 UYT 2021 by josedu
