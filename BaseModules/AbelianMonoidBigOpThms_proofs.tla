------------------- MODULE AbelianMonoidBigOpThms_proofs --------------------

(* 
  This module proves properties for operator `^$\BigOp{m}{n}{f(i)}$^' 
  defined in module AbelianMonoidBigOp.
*) 

EXTENDS AbelianMonoidBigOp, MonoidBigOpThms

LOCAL INSTANCE NaturalsInduction
LOCAL INSTANCE ArithUtilsThms
LOCAL INSTANCE TLAPS

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
<1> DEFINE op(h(_)) == bigOp(m, n, h)
<1>            P(i) == op(f)[i] (\X) op(g)[i] = op(LAMBDA j : f(j) (\X) g(j))[i]
<1> SUFFICES \A i \in m..n : P(i) 
  BY n \in m..n DEF BigOp   
<1>1. P(m)
  <2>0. SUFFICES op(f)[m] (\X) op(g)[m] = op(LAMBDA j : f(j) (\X) g(j))[m]
    OBVIOUS
  <2>1. /\ op(f)[m] = f(m)  
        /\ op(g)[m] = g(m)     
        /\ op(LAMBDA j : f(j) (\X) g(j))[m] = f(m) (\X) g(m)         BY m \in m..n, bigOpBaseCase
  <2>E1. op(f)[m] (\X) op(g)[m] = f(m) (\X) g(m)                     BY <2>1
  <2>E2.                      @ = op(LAMBDA j : f(j) (\X) g(j))[m]   BY <2>1
  <2> QED
    BY <2>E1, <2>E2
<1>2. \A i \in (m+1)..n : P(i-1) => P(i)  
  <2>0. SUFFICES ASSUME NEW i \in (m+1)..n, 
                        op(f)[i-1] (\X) op(g)[i-1] = op(LAMBDA j : f(j) (\X) g(j))[i-1]
                 PROVE  op(f)[i] (\X) op(g)[i] = op(LAMBDA j : f(j) (\X) g(j))[i]
    OBVIOUS
  <2>1. i \in m..n /\ i # m  BY <2>0
  <2>2. /\ op(f)[i] = op(f)[i-1] (\X) f(i)
        /\ op(g)[i] = op(g)[i-1] (\X) g(i)
        /\ op(LAMBDA j : f(j) (\X) g(j))[i] = op(LAMBDA j : f(j) (\X) g(j))[i-1] (\X) (f(i) (\X) g(i)) 
    BY <2>1, bigOpRecStep
  <2>3. /\ op(f) \in [m..n -> D]
        /\ op(g) \in [m..n -> D]  BY bigOpType        
  <2> DEFINE a == f(i)
             b == g(i)      
             A == op(f)[i-1]
             B == op(g)[i-1]
             C == op(LAMBDA j : f(j) (\X) g(j))[i-1]   \* HI: A (\X) B = C
             F == op(LAMBDA j : f(j) (\X) g(j))[i]     \* Final step:  C (\X) (a (\X) b) = F        
  <2>4. /\ A \in D
        /\ B \in D    BY <2>1, <2>3, i-1 \in m..n
  <2>5. /\ a \in D 
        /\ b \in D    BY i \in Nat      
  <2> HIDE DEF a,b,A,B             
  <2>E1. op(f)[i] (\X) op(g)[i] = (A (\X) a) (\X) (B (\X) b)   BY <2>2 DEF a,b,A,B
  <2>E2.                      @ = A (\X) (a (\X) (B (\X) b))   BY <2>4, <2>5, OpClosure, OpAssociativity
  <2>E3.                      @ = A (\X) ((B (\X) b) (\X) a)   BY <2>4, <2>5, OpClosure, OpCommutativity 
  <2>E4.                      @ = A (\X) (B (\X) (b (\X) a))   BY <2>4, <2>5, OpClosure, OpAssociativity 
  <2>E5.                      @ = A (\X) (B (\X) (a (\X) b))   BY <2>4, <2>5, OpClosure, OpCommutativity   
  <2>E6.                      @ = (A (\X) B) (\X) (a (\X) b)   BY <2>4, <2>5, OpClosure, OpAssociativity  
  <2>E7.                      @ = C (\X) (a (\X) b)            BY <2>0 DEF A, B  \* HI
  <2>E8.                      @ = F                            BY <2>2 DEF a,b,A,B
  <2> QED  
    BY <2>E1, <2>E2, <2>E3, <2>E4, <2>E5, <2>E6, <2>E7, <2>E8
<1> HIDE DEF P
<1> QED 
  BY <1>1, <1>2, IntervalNatInduction, Isa

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
<1> SUFFICES BigOp(m,n,LAMBDA i : IF i # j THEN f(i) ELSE Id) = BigOp(m,n,f)
  BY DEF BigOpP    
<1>A. CASE m <= n
  <2> DEFINE C(i) == IF i # j THEN f(i) ELSE Id
             P(i) == bigOp(m,n,C)[i] = bigOp(m,n,f)[i]
  <2> SUFFICES \A k \in m..n : P(k) 
    BY <1>A, n \in m..n DEF BigOp   
  <2>1. P(m)
    <3>0. SUFFICES bigOp(m,n,C)[m] = bigOp(m,n,f)[m]
      OBVIOUS
    <3>1. bigOp(m,n,C)[m] = f(m)    BY <1>A, m \in m..n, bigOpBaseCase
    <3>2. bigOp(m,n,f)[m] = f(m)    BY <1>A, m \in m..n, bigOpBaseCase      
    <3> QED 
      BY <3>1, <3>2
  <2>2. \A i \in (m+1)..n : P(i-1) => P(i)  
    <3>0. SUFFICES ASSUME NEW i \in (m+1)..n, 
                          bigOp(m,n,C)[i-1] = bigOp(m,n,f)[i-1]
                   PROVE  bigOp(m,n,C)[i]   = bigOp(m,n,f)[i]
      OBVIOUS
    <3>1. i \in m..n /\ i # m                             BY <3>0   
    <3>2. \A x \in m..n : C(x) \in D                      BY OpIdentity  
    <3>3. \A x \in m..n : C(x) = f(x)                     OBVIOUS    
    <3> HIDE DEF C
    <3>E1. bigOp(m,n,C)[i] = bigOp(m,n,C)[i-1] (\X) C(i)  BY <3>1, bigOpRecStep
    <3>E2.               @ = bigOp(m,n,f)[i-1] (\X) C(i)  BY <3>0 \* HI
    <3>E3.               @ = bigOp(m,n,f)[i-1] (\X) f(i)  BY <3>3, i \in m..n
    <3>E4.               @ = bigOp(m,n,f)[i]              BY <3>1, bigOpRecStep
    <3> QED 
      BY <3>E1, <3>E2, <3>E3, <3>E4 
  <2> HIDE DEF P
  <2> QED 
    BY <2>1, <2>2, IntervalNatInduction, Isa  
<1>B. CASE n < m
  BY <1>B DEF BigOp
<1> QED
  BY <1>A, <1>B

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
<1> DEFINE If(cnd,e1,e2) == IF cnd THEN e1 ELSE e2   
                    A(i) == If(i # j, f(i), Id)
                B(m0,n0) == BigOp(m0, n0, A)
<1>0. SUFFICES BigOp(m,n,f) = BigOp(m,n,LAMBDA i : If(i # j,f(i),Id)) (\X) f(j)
  BY DEF BigOpP   
<1>1. /\ \A i \in m..n :   A(i) \in D
      /\ \A i \in m..j :   A(i) \in D
      /\ \A i \in m..j-1 : A(i) \in D
      /\ \A i \in j+1..n : A(i) \in D
      /\ \A x \in m..j :   f(x) \in D
      /\ \A x \in m..j-1 : f(x) \in D
      /\ \A x \in j+1..n : f(x) \in D
  BY OpIdentity
<1>2. B(j+1,n) \in D                         
  BY <1>1, j+1 \in Nat, BigOpType
<1>3. B(m,j-1) \in D                        
  <3>A. CASE m <= j-1
    BY <1>1, <3>A, j-1 \in Nat, BigOpType
  <3>B. CASE m > j-1
    BY <3>B, m \in Int, j-1 \in Int, OpIdentity DEF BigOp
  <3> QED
    BY <3>A, <3>B    
<1>4. B(m,j-1) = BigOp(m,j-1,f)
  <3>A. CASE m <= j-1
    BY <1>1, <3>A, j-1 \in Nat, j \notin m..j-1, SkipOutOfBounds DEF BigOpP
  <3>B. CASE m > j-1
    BY <3>B, m \in Int, j-1 \in Int DEF BigOp
  <3> QED
    BY <3>A, <3>B
<1> HIDE DEF If, A, B
<1>E1. B(m,n) (\X) f(j) = (B(m,j) (\X) B(j+1,n)) (\X) f(j)                 BY <1>1, j \in m..n, SplitUp DEF B
<1>E2.                @ = ((B(m,j-1) (\X) A(j)) (\X) B(j+1,n)) (\X) f(j)   BY <1>1, j \in Nat, m <= j, SplitLast DEF B
<1>E3.                @ = ((B(m,j-1) (\X) Id) (\X) B(j+1,n)) (\X) f(j)     BY DEF If,A 
<1>E4.                @ = (B(m,j-1) (\X) B(j+1,n)) (\X) f(j)               BY <1>3, OpIdentity DEF B 
<1>E5.                @ = B(m,j-1) (\X) (B(j+1,n) (\X) f(j))               BY <1>2, <1>3, OpAssociativity DEF B   
<1>E6.                @ = B(m,j-1) (\X) (f(j) (\X) B(j+1,n))               BY <1>2, <1>3, OpCommutativity DEF B
<1>E7.                @ = (B(m,j-1) (\X) f(j)) (\X) B(j+1,n)               BY <1>2, <1>3, OpAssociativity DEF B 
<1>E8.                @ = (BigOp(m,j-1,f) (\X) f(j)) (\X) B(j+1,n)         BY <1>4
<1>E9.                @ = (BigOp(m,j-1,f) (\X) f(j)) (\X) BigOp(j+1,n,f)   BY <1>1, j+1 \in Nat, j \notin j+1..n, SkipOutOfBounds DEF BigOpP,B,A,If
<1>E10.               @ = BigOp(m,j,f) (\X) BigOp(j+1,n,f)                 BY <1>1, j \in Nat, j \in m..j, m <= j, SplitLast
<1>E11.               @ = BigOp(m,n,f)                                     BY j \in m..n, SplitUp
<1> QED
  BY <1>E1, <1>E2, <1>E3, <1>E4, <1>E5, <1>E6, <1>E7, 
     <1>E8, <1>E9, <1>E10, <1>E11 DEF B, A, If     

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
         NEW f(_), \A i \in {j \in m..n : P(j)} : f(i) \in D,   
         NEW j \in m..n, P(j),
         m <= n
  PROVE BigOpP(m,n,P,f) = BigOpP(m,n,LAMBDA i : P(i) /\ i # j, f) (\X) f(j)
<1>  DEFINE If(cnd,e1,e2) == IF cnd THEN e1 ELSE e2   
                    Cf(i) == If(P(i), f(i), Id)
                    R1(i) == i # j /\ P(i)
                    R2(i) == P(i) /\ i # j  
<1>1. \A i \in m..n : Cf(i) \in D 
  BY OpIdentity  
<1>2. /\ \A i \in m..n : R1(i) \in BOOLEAN 
      /\ \A i \in m..n : R2(i) \in BOOLEAN 
      /\ \A i \in m..n : R1(i) <=> R2(i)     OBVIOUS
<1>3. \A i \in {k \in m..n : R1(k) /\ R2(k)} : f(i) \in D BY <1>2
<1> HIDE DEF If,Cf,R1,R2
<1>4. BigOpP(m,n,R1,f) = BigOpP(m,n,R2,f)                                      BY <1>2, <1>3, PredicateEq, IsaM("blast") 
<1>E1. BigOpP(m,n,P,f) = BigOp(m,n,Cf)                                         BY DEF BigOpP,If,Cf
<1>E2.               @ = BigOpP(m,n,LAMBDA i : i # j, Cf) (\X) Cf(j)           BY <1>1, SplitRandom
<1>E3.               @ = BigOp(m,n,LAMBDA i : If(i # j,Cf(i),Id)) (\X) Cf(j)   BY DEF BigOpP,If,Cf
<1>E4.               @ = BigOp(m,n,LAMBDA i : If(R1(i),f(i),Id)) (\X) Cf(j)    BY DEF If,Cf,R1
<1>E5.               @ = BigOp(m,n,LAMBDA i : If(R1(i),f(i),Id)) (\X) f(j)     BY DEF If,Cf,R1
<1>E6.               @ = BigOpP(m,n,R1,f) (\X) f(j)                            BY DEF BigOpP,If,Cf,R1
<1>E7.               @ = BigOpP(m,n,R2,f) (\X) f(j)                            BY <1>4
<1> QED  
  BY <1>E1, <1>E2, <1>E3, <1>E4, <1>E5, <1>E6, <1>E7 DEF R2

=============================================================================
\* Modification History
\* Last modified Wed Aug 04 17:08:21 UYT 2021 by josedu
\* Last modified Fri Jul 02 00:31:15 GMT-03:00 2021 by JosEdu
\* Created Fri Jan 22 21:52:21 UYT 2021 by josedu
