---------------------------- MODULE MonoidBigOp ----------------------------

(* 
  Let `^$(D, Id, \otimes)$^' be a Monoid structure. This module
  defines the extension of binary operation `^$\otimes$^' over 
  finite intervals.
  
  See relevant theorems in module MonoidBigOpThms.
*) 

EXTENDS AbstractAlgebra

LOCAL INSTANCE Naturals

----------------------------------------------------------------------------

(* 
  This module is parameterized by the signature `^$(D, Id, \otimes)$^'.
  
  Is taken as an assumption that `^$(D, Id, \otimes)$^' obeys the laws
  of a Monoid.
*) 

CONSTANTS D,         \* Domain
          Id,        \* Special constant symbol
          _(\X)_     \* Binary operator

AXIOM Algebra == Monoid(D, Id, (\X))

----------------------------------------------------------------------------

(* 
  The operation `^$\otimes$^' over (non empty) interval `^$m..n$^' 
  defined as a recursive function

  `^\displaystyle\quad 
      \bigOp{m}{n}{f} \ : \ m..n \to D^'   
*) 
bigOp(m,n,f(_)) ==
  LET recDef[i \in m..n] ==
        IF i = m 
        THEN f(m)
        ELSE recDef[i-1] (\X) f(i)
  IN recDef  

(* 
  When `^$m > n$^', and thus interval `^$m..n$^' is empty, it is assumed the 
  result is the monoid identity `^$Id$^'. The result of the operation `^$\otimes$^' 
  over interval `^$m..n$^' is denoted by

  `^\displaystyle\quad
      \BigOp{m}{n}{f(i)} \ \defeq \ \left(\bigOp{m}{n}{f}\right) [n]^'
*) 
BigOp(m,n,f(_)) == 
  IF m <= n 
  THEN bigOp(m,n,f)[n] 
  ELSE Id

(*   
  A convenient abbreviation to deal with holes in the interval:

  `^\displaystyle\quad
      \BigOpP{m}{n}{P(i)}{f(i)} \ \defeq \ \BigOp{m}{n}{(P(i) \to f(i),\ Id)}^'      
*)

BigOpP(m,n,P(_),f(_)) == BigOp(m,n,LAMBDA i : IF P(i) THEN f(i) ELSE Id)

============================================================================
\* Modification History
\* Last modified Thu Sep 02 21:16:02 UYT 2021 by josedu
\* Last modified Mon Jun 28 21:34:03 GMT-03:00 2021 by JosEdu
\* Created Tue Jan 05 21:31:32 UYT 2021 by josedu
