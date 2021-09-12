------------------------ MODULE PCR_FibPrimes2 ------------------------------

(*
  PCR FibPrimes2.
   
  `.-----------------------------------------------------------------
    fun fibs(p,i)  = if i <= 2 then 1 else p[-1] + p[-2] 
    fun count(r,c) = r + if c then 1 else 0 
   
    dep p(i-1) -> p(i)
    dep p(i-2) -> p(i)
   
    lbnd FibPrimes1 = \N. 1
    ubnd FibPrimes1 = \N. x 
   
    PCR FibPrimes2(N)
      par
        p1 = produce fibs p1
        c1 = consume IsPrime p1
        r1 = reduce count 0 c1
            
    fun divs(i)     = i
    fun notDiv(F,p) = F > 1 and (p > 1 implies not divides(p,F))
   
    lbnd IsPrime2 = \F. 0
    ubnd IsPrime2 = \F. sqrt(F)  
    prop IsPrime2 = \i. i <= 2 or odd(i)
   
    PCR IsPrime2(F)
      par
        p2 = produce divs p2
        c2 = consume notDiv F p2
        r2 = reduce and true c2          
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  Concrete elements of FibPrimes2
*)

T   == Nat
Tp1 == Nat
Tc1 == BOOLEAN
D1  == Nat

Dep_pp1 == <<{1,2},{}>>
Dep_pc1 == <<{},{}>>
Dep_cr1 == <<{},{}>>

lBnd1(N) == 1
uBnd1(N) == N
prop1(i) == TRUE

fibs(p,i) == IF i <= 2 THEN 1 ELSE p[i-1] + p[i-2]
toNat(c)  == IF c THEN 1 ELSE 0

id1      == 0
Op1(x,y) == x + y

(* 
  Concrete elements of IsPrime2
*)

Tp2 == Nat
Tc2 == BOOLEAN
D2  == BOOLEAN

Dep_pp2 == <<{},{}>>
Dep_pc2 == <<{},{}>>
Dep_cr2 == <<{},{}>>

lBnd2(F) == 0
uBnd2(F) == Sqrt(F)
prop2(i) == i <= 2 \/ Odd(i)

divs(i)     == i
notDiv(F,p) == F > 1 /\ (p > 1 => ~ Divides(p,F))

id2      == TRUE
Op2(x,y) == x /\ y

----------------------------------------------------------------------------

(* 
  FibPrimes2 is a concrete instance of the abstract model PCR_A_c_B
*)

VARIABLES in, X1, p1, c1, r1, rs1,
              X2, p2, c2, r2, rs2

I0      == <<>>
pre(x1) == TRUE

fp1(x1,vp,i) == fibs(vp,i) 
fr1(x1,vc,i) == toNat(vc[i])
gp1(x1,i)    == fibonacci[i]

_uBnd2(x2)   == LET F == x2[2][x2[3]] IN uBnd2(F) 
fp2(x2,vp,i) == divs(i) 
fc2(x2,vp,i) == LET F == x2[2][x2[3]] IN notDiv(F,vp[i])
fr2(x2,vc,i) == vc[i]
gp2(x2,i)    == fp2(x2,p2,i)

INSTANCE PCR_A_c_B WITH uBnd2 <- _uBnd2

----------------------------------------------------------------------------

(* 
  Alternative correctness
*)

CountFibPrimes(N) == LET fibSeq == [i \in 1..N |-> fibonacci[i]]
                     IN  Len(SelectSeq(fibSeq, LAMBDA f : IsPrime(f)))           

CorrectnessAlt == endA(I0) => r1[I0] = CountFibPrimes(X1[I0])

=============================================================================
