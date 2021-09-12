---------------------------- MODULE PCR_IsPrime2 ----------------------------

(*
  PCR IsPrime2.
   
  `.-----------------------------------------------------------------
    fun divs(i)     = i
    fun notDiv(N,p) = N > 1 and (p > 1 implies not divides(p,N))
   
    lbnd IsPrime2 = \N. 0
    ubnd IsPrime2 = \N. sqrt(N)  
    prop IsPrime2 = \i. i <= 2 or odd(i)
   
    PCR IsPrime2(N)
      par
        p = produce divs p
        c = consume notDiv N p
        r = reduce and true c
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  Concrete elements of IsPrime2
*)

T  == Nat
Tp == Nat
Tc == BOOLEAN
D  == BOOLEAN

Dep_pp == <<{},{}>>
Dep_pc == <<{},{}>>
Dep_cr == <<{},{}>>

lBnd(N) == 0
uBnd(N) == Sqrt(N)
prop(i) == i <= 2 \/ Odd(i)

divs(i)     == i
notDiv(N,p) == N > 1 /\ (p > 1 => ~ Divides(p,N))

id      == TRUE
Op(x,y) == x /\ y

----------------------------------------------------------------------------

(* 
  IsPrime2 is a concrete instance of the abstract model PCR_A
*)

VARIABLES in, X, p, c, r, rs

I0     == <<>>
pre(x) == TRUE

fp(x,vp,i) == divs(i) 
fc(x,vp,i) == notDiv(x,vp[i])
fr(x,vc,i) == vc[i]
gp(x,i)    == fp(x,p,i)

INSTANCE PCR_A

----------------------------------------------------------------------------

(* 
  Alternative correctness
*)

CorrectnessAlt == end(I0) => r[I0] = IsPrime(X[I0])
         
=============================================================================
