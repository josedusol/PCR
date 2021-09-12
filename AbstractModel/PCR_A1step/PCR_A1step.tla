------------------------- MODULE PCR_A1step --------------------------------

(*
  Basic PCR as a one step computation.
   
  `.----------------------------------------------------------------- 
    fun fp(x,p,i) = ...               // fp : T x St(Tp) x N -> Tp 
    fun fc(x,p,i) = ...               // fc : T x St(Tp) x N -> Tc
    fun fr(x,c,i) = ...               // fr : T x St(Tc) x N -> D  
   
    dep p(i-k) -> p(i)
    dep p(i[+/-]k) -> c(i)
    dep c(i[+/-]k) -> r(i)
   
    lbnd A = \x. ...
    ubnd A = \x. ... 
    prop A = \i. ... 
   
    PCR A(x)                          // x \in T
      par
        p = produce fp x p
        c = consume fc x p
        r = reduce  Op id (fr x c)    // r \in D 
  -----------------------------------------------------------------.'  
*)

EXTENDS AbstractAlgebra, Naturals, Sequences, Bags, SeqUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  PCR constants and variables
*)

CONSTANTS pre(_),             
          T, D,
          id, Op(_,_),
          lBnd(_), uBnd(_), prop(_),
          fp(_,_,_), fc(_,_,_), fr(_,_,_), gp(_,_)

VARIABLES in, out
 
----------------------------------------------------------------------------

(* 
  PCR definitions
*)

Assig == Nat

M == INSTANCE AbelianMonoidBigOp
  WITH D <- D, Id <- id, \otimes <- Op 

Gp(x)    == [i \in Assig |-> gp(x,i)]
Fc(x,vp) == [i \in Assig |-> fc(x,vp,i)]
Fr(x,vc) == [i \in Assig |-> fr(x,vc,i)]

A(x) == M!BigOpP(lBnd(x), uBnd(x), prop, LAMBDA i : Fr(x,Fc(x,Gp(x)))[i])

----------------------------------------------------------------------------

(* 
  Operational specification
*)

vs == <<in,out>>

Init == /\ in \in T 
        /\ pre(in) 
        /\ out = id 

Next == /\ out' = A(in)
        /\ UNCHANGED in
\*        /\ PrintT("Done: In = " \o ToString(in)
\*                 \o " - Out = " \o ToString(out))

Spec == Init /\ [][Next]_vs

FairSpec == Spec /\ WF_vs(Next)

----------------------------------------------------------------------------

(* 
  Properties
*)

Termination == <>(out = A(in))       

============================================================================
\* Modification History
\* Last modified Wed Sep 08 18:29:03 UYT 2021 by josedu
\* Last modified Wed Jul 07 17:27:06 GMT-03:00 2021 by JosEdu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
