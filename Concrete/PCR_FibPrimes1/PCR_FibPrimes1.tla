------------------------ MODULE PCR_FibPrimes1 ------------------------------

(*
  PCR FibPrimes1.
   
  `.-----------------------------------------------------------------
    fun fibs(p,i)  = if i <= 2 then 1 else p[-1] + p[-2] 
    fun isPrime(p) = n > 1 and not (some (\m. divides(m,n)) [2..n-1])
    fun count(r,c) = r + if c then 1 else 0 
   
    dep p(i-1) -> p(i)
    dep p(i-2) -> p(i)
   
    lbnd FibPrimes1 = \N. 1
    ubnd FibPrimes1 = \N. x 
   
    PCR FibPrimes1(N)
      par
        p = produce fibs p
        c = consume isPrime p
        r = reduce count 0 c
  -----------------------------------------------------------------.'  
*)

EXTENDS Naturals, Sequences, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  Concrete elements of FibPrimes1
*)

T  == Nat
Tp == Nat
Tc == BOOLEAN
D  == Nat

Dep_pp == <<{1,2},{}>>
Dep_pc == <<{},{}>>
Dep_cr == <<{},{}>>

lBnd(N) == 1
uBnd(N) == N
prop(i) == TRUE

fibs(p,i)  == IF i <= 2 THEN 1 ELSE p[i-1] + p[i-2]
isPrime(p) == p > 1 /\ ~ \E m \in 2..(p-1) : Divides(m,p)
toNat(c)   == IF c THEN 1 ELSE 0

id      == 0
Op(x,y) == x + y

----------------------------------------------------------------------------

(* 
  FibPrimes1 is a concrete instance of the abstract model PCR_A
*)

VARIABLES in, X, p, c, r, rs

I0     == <<>>
pre(x) == TRUE

fp(x,vp,i) == fibs(vp,i) 
fc(x,vp,i) == isPrime(vp[i])
fr(x,vc,i) == toNat(vc[i])
gp(x,i)    == fibonacci[i]

INSTANCE PCR_A_Thms

----------------------------------------------------------------------------

(* 
  Most axioms can be promoted to ordinary mathematical lemmas. 
  These are proved in module PCR_FibPrimes1_Lems.
*)

Lem_Type        == H_Type
Lem_BFunWD      == H_BFunWD
Lem_fpRelevance == H_fpRelevance
Lem_fcRelevance == H_fcRelevance
Lem_frRelevance == H_frRelevance
Lem_Algebra     == H_Algebra

(* 
  The invariant axiom for the producer can be proved alongside the other
  basic invariants. This is done in module PCR_FibPrimes1_Thms.
*)       
  
ProdEqInv == 
  \A i \in It(X[I0]) :
    wrt(p[I0][i]) => fp(X[I0],p[I0],i) = gp(X[I0],i)

(* 
  The ordinary lemmas re-stated as invariant properties for model checking.
  
  They are relativized to I0 for a more tractable verification,
  but even so it is only feasible for very small bounds.
*)

TypeCheck ==
  /\ lBnd(X[I0]) \in Nat
  /\ uBnd(X[I0]) \in Nat
  /\ prop(X[I0]) \in BOOLEAN
  /\ pre(X[I0])  \in BOOLEAN
  /\ Dep_pp \in (SUBSET (Nat\{0})) \X (SUBSET {})
  /\ Dep_pc \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))
  /\ Dep_cr \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))  

BFunWDCheck == 
  \A i \in It(X[I0]) :  
    /\ gp(X[I0],i) \in Tp
    /\ wrts(p[I0],deps(X[I0],Dep_pp,i)\{i}) => fp(X[I0],p[I0],i) \in Tp
    /\ wrts(p[I0],deps(X[I0],Dep_pc,i))     => fc(X[I0],p[I0],i) \in Tc
    /\ wrts(c[I0],deps(X[I0],Dep_cr,i))     => fr(X[I0],c[I0],i) \in D

fpRelevanceCheck == 
  \A i \in It(X[I0]), vp1 \in St(Tp), vp2 \in St(Tp) :
    eqs(vp1,vp2,deps(X[I0],Dep_pp,i)\{i}) => fp(X[I0],vp1,i) = fp(X[I0],vp2,i)

fcRelevanceCheck == 
  \A i \in It(X[I0]), vp1 \in St(Tp), vp2 \in St(Tp) :     
    eqs(vp1,vp2,deps(X[I0],Dep_pc,i)) => fc(X[I0],vp1,i) = fc(X[I0],vp2,i)
      
frRelevanceCheck == 
  \A i \in It(X[I0]), vc1 \in St(Tc), vc2 \in St(Tc) :
    eqs(vc1,vc2,deps(X[I0],Dep_cr,i)) => fr(X[I0],vc1,i) = fr(X[I0],vc2,i)      

LemmaCheck == /\ TypeCheck
              /\ BFunWDCheck
              /\ fpRelevanceCheck
              /\ fcRelevanceCheck
              /\ frRelevanceCheck

(* 
  Alternative correctness
*)

CountFibPrimes(N) == LET fibSeq == [i \in 1..N |-> fibonacci[i]]
                     IN  Len(SelectSeq(fibSeq, LAMBDA f : IsPrime(f)))           

CorrectnessAlt == end(I0) => r[I0] = CountFibPrimes(X[I0])

=============================================================================
