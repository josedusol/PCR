----------------------- MODULE MonoidBigOpThms_proofs -----------------------

(* 
  Proofs of theorems in module AbelianMonoidBigOp.
*) 

EXTENDS MonoidBigOp

LOCAL INSTANCE Naturals
LOCAL INSTANCE NaturalsInduction
LOCAL INSTANCE ArithUtilsThms
LOCAL INSTANCE TLAPS

-----------------------------------------------------------------------------
  
(* 
  The following theorems asserts that our definition of bigOp is well defined, 
  that is, there exists a function matching the recursive definition.
*)

LEMMA bigOpDefConclusion ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW f(_)
  PROVE FiniteNatInductiveDefConclusion(bigOp(m,n,f), f(m), LAMBDA v,i : v (\X) f(i), m, n) 
<1>1. FiniteNatInductiveDefHypothesis(bigOp(m,n,f), f(m), LAMBDA v,i : v (\X) f(i), m, n)
  BY DEF FiniteNatInductiveDefHypothesis, bigOp 
<1>2. QED
  BY <1>1, FiniteNatInductiveDef

THEOREM bigOpDef ==
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW f(_),  
         NEW i \in m..n
  PROVE bigOp(m,n,f)[i] = IF i = m THEN f(m) ELSE bigOp(m,n,f)[i-1] (\X) f(i)
<1> DEFINE g == bigOp(m,n,f) 
<1> SUFFICES g[i] = IF i = m THEN f(m) ELSE g[i-1] (\X) f(i)
  OBVIOUS  
<1>1. FiniteNatInductiveDefConclusion(g, f(m), LAMBDA v,i2 : v (\X) f(i2), m, n)    
  BY bigOpDefConclusion
<1> HIDE DEF g  
<1> QED  
  BY <1>1 DEF FiniteNatInductiveDefConclusion, Isa

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
<1> DEFINE g == bigOp(m,n,f)  
<1> SUFFICES g \in [m..n -> D] 
  OBVIOUS                  
<1>1. f(m) \in D
  OBVIOUS
<1>2. \A v \in D : \A i \in (m+1)..n : v (\X) f(i) \in D
  BY Algebra DEF Monoid, SemiGroup, Magma
<1>3. FiniteNatInductiveDefConclusion(g, f(m), LAMBDA v,i : v (\X) f(i), m, n) 
  BY bigOpDefConclusion
<1> HIDE DEF g  
<1> QED
  BY <1>1, <1>2, <1>3, FiniteNatInductiveDefType, Isa

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
<1> DEFINE g == bigOp(m, n, f)
<1>1. g[i] = IF i = m THEN f(m) ELSE g[i-1] (\X) f(i)   BY bigOpDef, Isa
<1>2. g[i] = f(m)                                       BY <1>1
<1> QED  
  BY <1>2  

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
<1> DEFINE g == bigOp(m, n, f)
<1>1. g[i] = IF i = m THEN f(m) ELSE g[i-1] (\X) f(i)   BY bigOpDef, Isa
<1>2. g[i] = g[i-1] (\X) f(i)                           BY <1>1 
<1> QED  
  BY <1>2   

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
<1>A. CASE m <= n  
  <2>1. bigOp(m,n,f) \in [m..n -> D]
    BY <1>A, bigOpType, Isa 
  <2>2. bigOp(m,n,f)[n] \in D
    BY <1>A, <2>1
  <2> QED
    BY <1>A, <2>2 DEF BigOp 
<1>B. CASE n < m
  <2>1. BigOp(m,n,f) = Id
    BY <1>B DEF BigOp
  <2> QED 
    BY <2>1, Algebra DEF Monoid
<1> QED 
  BY <1>A, <1>B

-----------------------------------------------------------------------------

(* 
  The (assumed) monoid laws for binary operator `^$\otimes$^'. 
*) 

PROPOSITION OpClosure == 
  \A x, y \in D : x (\X) y \in D
  BY Algebra DEF Monoid, SemiGroup, Magma

PROPOSITION OpAssociativity == 
  \A x, y, z \in D : (x (\X) y) (\X) z = x (\X) (y (\X) z)
  BY Algebra DEF Monoid, SemiGroup

PROPOSITION OpIdentity == 
  \E e \in D : \A x \in D : /\ e = Id 
                            /\ x  (\X) Id = x 
                            /\ Id (\X) x  = x
  BY Algebra DEF Monoid  

THEOREM OpUniqueIdentity == 
  ASSUME NEW e1, NEW e2,
         \A x : x (\X) e1 = x /\ e1 (\X) x = x,
         \A x : x (\X) e2 = x /\ e2 (\X) x = x
  PROVE  e1 = e2
  BY MonoidUniqueIdentity  

PROPOSITION OpIdentityLeft == 
  \A x \in D : Id (\X) x = x
  BY OpIdentity    
  
PROPOSITION OpIdentityRight == 
  \A x \in D : x (\X) Id = x
  BY OpIdentity 

-----------------------------------------------------------------------------

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
<1> DEFINE P(k) == \A i \in m..k : bigOp(m,k,f)[i] = bigOp(m,i,f)[i]
<1> SUFFICES \A k \in m..n : P(k) 
  OBVIOUS   
<1>1. ASSUME NEW k \in m..n
      PROVE (\A j \in m..(k-1) : P(j)) => P(k)
  <2>0. SUFFICES ASSUME \A j \in m..(k-1) : \A i \in m..j : bigOp(m,j,f)[i] = bigOp(m,i,f)[i]
                 PROVE  \A i \in m..k : bigOp(m,k,f)[i] = bigOp(m,i,f)[i]
    OBVIOUS
  <2> DEFINE Q(i) == bigOp(m,k,f)[i] = bigOp(m,i,f)[i]
  <2> SUFFICES  \A i \in m..k : Q(i)
    OBVIOUS 
  <2>1. Q(m)
    <3>0. SUFFICES bigOp(m,k,f)[m] = bigOp(m,m,f)[m] 
      OBVIOUS
    <3>1. bigOp(m,k,f)[m] = f(m)    BY k \in Nat, m \in m..k, bigOpBaseCase
    <3>2. bigOp(m,m,f)[m] = f(m)    BY k \in Nat, m \in m..m, bigOpBaseCase      
    <3> QED 
      BY <3>1, <3>2
  <2>2. \A i \in (m+1)..k : Q(i-1) => Q(i) 
    <3>0. SUFFICES ASSUME NEW i \in (m+1)..k, 
                          bigOp(m,k,f)[i-1] = bigOp(m,i-1,f)[i-1]
                   PROVE  bigOp(m,k,f)[i] = bigOp(m,i,f)[i]
      OBVIOUS
    <3>1. i \in Nat /\ k \in Nat /\ i \in m..k /\ i # m  BY <3>0   
    <3>A. CASE i = k
      <4>1. bigOp(m,k,f)[k] = bigOp(m,k,f)[k]            BY <3>A
      <4> QED
        BY <3>A, <4>1    
    <3>B. CASE i \in (m+1)..(k-1)   
      <4>1. /\ \A x \in m..k : f(x) \in D   
            /\ \A x \in m..i : f(x) \in D      BY <3>B, m..k \subseteq m..n, m..i \subseteq m..n    
      <4>2. /\ bigOp(m,k,f) \in [m..k -> D]   
            /\ bigOp(m,i,f) \in [m..i -> D]    BY <3>1, <4>1, m <= k, m <= i, bigOpType, Isa              
      <4>3. bigOp(m,i,f)[i-1] = bigOp(m,i-1,f)[i-1]             BY <3>B, <2>0      
      <4>E1. bigOp(m,k,f)[i] = bigOp(m,k,f)[i-1]   (\X) f(i)    BY <3>1, <4>2, bigOpRecStep
      <4>E2.               @ = bigOp(m,i-1,f)[i-1] (\X) f(i)    BY <3>0  \* HI
      <4>E3.               @ = bigOp(m,i,f)[i-1]   (\X) f(i)    BY <4>3
      <4>E4.               @ = bigOp(m,i,f)[i]                  BY <3>1, <4>2, i \in m..i, bigOpRecStep     
      <4> QED
        BY <4>E1, <4>E2, <4>E3, <4>E4
    <3> QED  
      BY <3>A, <3>B   
  <2> HIDE DEF P, Q 
  <2> QED
     BY <2>1, <2>2, k \in Nat, IntervalNatInduction, Isa
<1> HIDE DEF P
<1> QED 
  BY <1>1, IntervalGeneralNatInduction, IsaM("blast")

(*
  BigOp over constant identity.
  
  `^\displaystyle\quad
      \BigOp{m}{n}{Id} = Id^'
*)
THEOREM OpIdentityExt == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat
  PROVE BigOp(m,n,LAMBDA i : Id) = Id
<1>A. CASE m <= n    
  <2> DEFINE f(i) == Id
             P(i) == bigOp(m,n,f)[i] = Id
  <2> SUFFICES \A i \in m..n : P(i) 
    BY <1>A, n \in m..n DEF BigOp   
  <2>1. P(m)
    <3>0. SUFFICES bigOp(m,n,f)[m] = Id
      OBVIOUS
    <3>1. bigOp(m,n,f)[m] = Id    BY <1>A, m \in m..n, bigOpBaseCase
    <3> QED 
      BY <3>1
  <2>2. \A i \in (m+1)..n : P(i-1) => P(i)  
    <3>0. SUFFICES ASSUME NEW i \in (m+1)..n, 
                          bigOp(m,n,f)[i-1] = Id
                   PROVE  bigOp(m,n,f)[i]   = Id
      OBVIOUS
    <3>1. i \in m..n /\ i # m                             BY <3>0   
    <3> HIDE DEF f
    <3>E1. bigOp(m,n,f)[i] = bigOp(m,n,f)[i-1] (\X) f(i)  BY <3>1, bigOpRecStep
    <3>E2.               @ = bigOp(m,n,f)[i-1] (\X) Id    BY DEF f
    <3>E3.               @ = Id (\X) Id                   BY <3>0  \* HI  
    <3>E4.               @ = Id                           BY OpIdentity
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
<1>A. CASE m <= n  
  <2> DEFINE P(i) == bigOp(m,n,f)[i] = bigOp(m,n,g)[i]
  <2> SUFFICES \A i \in m..n : P(i) 
    BY <1>A, n \in m..n DEF BigOp   
  <2>1. P(m)
    <3>0. SUFFICES bigOp(m,n,f)[m] = bigOp(m,n,g)[m]
      OBVIOUS
    <3>1. bigOp(m,n,f)[m] = f(m)    BY <1>A, m \in m..n, bigOpBaseCase
    <3>2. bigOp(m,n,g)[m] = f(m)    BY <1>A, m \in m..n, bigOpBaseCase      
    <3> QED 
      BY <3>1, <3>2
  <2>2. \A i \in (m+1)..n : P(i-1) => P(i)
    <3>0. SUFFICES ASSUME NEW i \in (m+1)..n, 
                          bigOp(m,n,f)[i-1] = bigOp(m,n,g)[i-1]
                   PROVE  bigOp(m,n,f)[i] = bigOp(m,n,g)[i]
      OBVIOUS
    <3>1. i \in m..n /\ i # m                    BY <3>0     
    <3>2. /\ bigOp(m,n,f) \in [m..n -> D]
          /\ bigOp(m,n,g) \in [m..n -> D]      BY <1>A, bigOpType, Isa    
    <3>E1. bigOp(m,n,f)[i] = bigOp(m,n,f)[i-1] (\X) f(i) BY <3>1, <3>2, bigOpRecStep
    <3>E2.               @ = bigOp(m,n,g)[i-1] (\X) f(i) BY <3>0
    <3>E3.               @ = bigOp(m,n,g)[i-1] (\X) g(i) BY <3>1
    <3>E4.               @ = bigOp(m,n,g)[i]             BY <3>1, <3>2, bigOpRecStep  
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
  Operation over unitary interval is trivial.

  `^\displaystyle\quad
      \BigOp{n}{n}{f(i)} \ = \ f(n)^'   
*)
THEOREM UnitInterval == 
  ASSUME NEW n \in Nat, 
         NEW f(_)
  PROVE BigOp(n,n,f) = f(n)
<2>E1. BigOp(n,n,f) = bigOp(n,n,f)[n]    BY DEF BigOp
<2>E2.            @ = f(n)               BY n \in n..n, bigOpBaseCase
<2> QED 
  BY <2>E1, <2>E2                                                        

(* 
  For any `^$k \in m..n$^', operation can be split at `^$k$^'.

  `^\displaystyle\quad 
      \BigOp{m}{n}{f(i)} \ = \ \BigOp{m}{k}{f(i)} \ \otimes \ \BigOp{k+1}{n}{f(i)}^'               
*)
THEOREM SplitUp == 
  ASSUME NEW m \in Nat,
         NEW n \in Nat,    
         NEW f(_), \A x \in m..n : f(x) \in D,
         NEW k \in m..n,
         m <= n
  PROVE BigOp(m,n,f) = BigOp(m,k,f) (\X) BigOp(k+1,n,f)
<1>A. CASE k = n
  <2>1.  BigOp(m,n,f) \in D                                       BY BigOpType
  <2>E1. BigOp(m,n,f) (\X) BigOp(n+1,n,f) = BigOp(m,n,f) (\X) Id  BY DEF BigOp
  <2>E2.                                @ = BigOp(m,n,f)          BY <2>1, OpIdentity 
  <2> QED
    BY <1>A, <2>E1, <2>E2 
<1>B. CASE k \in m..n-1  
  <2> DEFINE P(i) == \A j \in m..i-1 : bigOp(m,n,f)[i] = bigOp(m,j,f)[j] (\X) bigOp(j+1,n,f)[i]
  <2> SUFFICES \A i \in m..n : P(i)  
    BY <1>B, n \in m..n DEF BigOp
  <2>1. P(m)
    <3>0. SUFFICES ASSUME NEW j \in m..m-1
                   PROVE  bigOp(m,n,f)[m] = bigOp(m,j,f)[j] (\X) bigOp(j+1,n,f)[m]
      OBVIOUS
    <3> QED BY <3>0
  <2>2. \A i \in (m+1)..n : P(i-1) => P(i) 
    <3>0. SUFFICES ASSUME NEW i \in (m+1)..n, 
                          \A j \in m..i-2 : bigOp(m,n,f)[i-1] = bigOp(m,j,f)[j] (\X) bigOp(j+1,n,f)[i-1]
                   PROVE  \A j \in m..i-1 : bigOp(m,n,f)[i]   = bigOp(m,j,f)[j] (\X) bigOp(j+1,n,f)[i]
      OBVIOUS            
    <3> TAKE h \in m..i-1
    <3>1. i \in Nat /\ i \in m..n /\ i # m     BY <3>0   
    <3>2. bigOp(m,n,f)[i] = bigOp(m,n,f)[i-1] (\X) f(i)
        BY <3>1, bigOpRecStep   
    <3>A. CASE h = i-1
      <4>0. SUFFICES bigOp(m,n,f)[i] = bigOp(m,i-1,f)[i-1] (\X) bigOp(i,n,f)[i]
        BY <3>A        
      <4>1. /\ \A x \in i..n :   f(x) \in D   
            /\ \A x \in m..i-1 : f(x) \in D     BY i..n \subseteq m..n, m..i-1 \subseteq m..n
      <4>2. bigOp(i,n,f)   \in [i..n -> D]      BY <3>1, <4>1, i <= n, bigOpType, Isa
      <4>3. bigOp(m,i-1,f) \in [m..i-1 -> D]    BY <3>1, <4>1, i-1 \in Nat, m <= i-1, bigOpType, Isa
      <4>4. bigOp(i,n,f)[i] = f(i)              BY <3>1, <4>1, i \in i..n, bigOpBaseCase, Isa
      <4> DEFINE a == f(i)     
                 A == bigOp(m,i-1,f)[i-1]
                 B == bigOp(m,n,f)[i-1]               
                 C == bigOp(m,n,f)[i]
      <4>5. A \in D                             BY <4>3
      <4>6. a \in D                             BY <3>1  
      <4> HIDE DEF a,A,B,C                     
      <4>E1. A (\X) bigOp(i,n,f)[i] = A (\X) a    BY <4>4 DEF a,A 
      <4>E2.                      @ = B (\X) a    BY i-1 \in Nat, i-1 \in m..n, BasicNotationalEq DEF A, B
      <4>E3.                      @ = C           BY <3>2 DEF a,B,C    
      <4> QED 
        BY <4>E1, <4>E2, <4>E3 DEF A, C  
    <3>B. CASE h \in m..i-2        
      <4>1. h \in Nat /\ i \in h+1..n /\ i # h+1  BY <3>B, <3>0             
      <4>2. bigOp(h+1,n,f)[i] = bigOp(h+1,n,f)[i-1] (\X) f(i)
        BY <4>1, h \in Nat, h+1 <= n, bigOpRecStep       
      <4>3. /\ \A x \in m..h :   f(x) \in D
            /\ \A x \in h+1..n : f(x) \in D          BY m..h \subseteq m..n, h+1..n \subseteq m..n                      
      <4>4. bigOp(m, n, f)   \in [m..n -> D]         BY m <= n, bigOpType, Isa
      <4>5. bigOp(m, h, f)   \in [m..h -> D]         BY <4>3, h \in Nat, m <= h, bigOpType, Isa
      <4>6. bigOp(h+1, n, f) \in [h+1..n -> D]       BY <4>3, h \in Nat, h+1 \in Nat, h+1 <= n, bigOpType, Isa       
      <4> DEFINE a == f(i)     
                 A == bigOp(m, h, f)[h]
                 B == bigOp(h+1, n, f)[i-1]
                 C == bigOp(h+1, n, f)[i]      \* Final step: B (\X) a = C                  
      <4>7. /\ A \in D 
            /\ B \in D                                   BY <4>1, <4>5, <4>6     
      <4>8. a \in D                                      BY <4>1  
      <4> HIDE DEF a,A,B              
      <4>E1. bigOp(m,n,f)[i] = bigOp(m,n,f)[i-1] (\X) a    BY <3>2 DEF a
      <4>E2.               @ = (A (\X) B) (\X) a           BY <3>B, <3>0 DEF A, B  \* HI
      <4>E3.               @ = A (\X) (B (\X) a)           BY <4>7, <4>8, OpClosure, OpAssociativity
      <4>E4.               @ = A (\X) C                    BY <4>2 DEF a, B, C        
      <4> QED 
        BY <4>E1, <4>E2, <4>E3, <4>E4 DEF A, C         
    <3> QED 
      BY <3>A, <3>B
  <2> HIDE DEF P
  <2> QED 
    BY <2>1, <2>2, IntervalNatInduction, Isa
<1> QED 
  BY <1>A, <1>B

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
         NEW k \in m..n,
         m <= n
  PROVE BigOp(m,n,f) = BigOp(m,k-1,f) (\X) BigOp(k,n,f)
<1>A. CASE k = m
  <2>1.  BigOp(m,n,f) \in D                                       BY BigOpType
  <2>E1. BigOp(m,m-1,f) (\X) BigOp(m,n,f) = Id (\X) BigOp(m,n,f)  BY DEF BigOp
  <2>E2.                                @ = BigOp(m,n,f)          BY <2>1, OpIdentity 
  <2> QED
    BY <1>A, <2>E1, <2>E2  
<1>B. CASE k \in m+1..n
  <2>1. \A j \in m..n : BigOp(m,n,f) = BigOp(m,j,f) (\X) BigOp(j+1,n,f)  BY SplitUp, Isa
  <2>2. BigOp(m,n,f) = BigOp(m,k-1,f) (\X) BigOp(k,n,f)                  BY <1>B, <2>1
  <2> QED
    BY <2>2 
<1> QED 
  BY <1>A, <1>B

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
<1>2. \A j \in m..n : BigOp(m,n,f) = BigOp(m,j,f) (\X) BigOp(j+1,n,f)   BY m <= n, SplitUp, Isa
<1>E1. BigOp(m,n,f) = BigOp(m,m,f) (\X) BigOp(m+1,n,f)                  BY m \in m..n, <1>2 
<1>E2.            @ = f(m) (\X) BigOp(m+1,n,f)                          BY UnitInterval
<1> QED 
  BY <1>E1, <1>E2

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
<1>2. \A j \in m..n : BigOp(m,n,f) = BigOp(m,j-1,f) (\X) BigOp(j,n,f)   BY m <= n, SplitDown, Isa
<1>E1. BigOp(m,n,f) = BigOp(m,n-1,f) (\X) BigOp(n,n,f)                  BY n \in m..n, <1>2 
<1>E2.            @ = BigOp(m,n-1,f) (\X) f(n)                          BY UnitInterval
<1> QED 
  BY <1>E1, <1>E2

-----------------------------------------------------------------------------

(* 
  When `^$m > n$^', and thus inverval `^$m..n$^' is empty, it is assumed the 
  result is the monoid identity `^$Id$^'.
*)
COROLLARY EmptyIntervalAssumptionP ==  
  ASSUME NEW m \in Nat,
         NEW n \in Nat,
         NEW P(_),
         NEW f(_),
         n < m
  PROVE  BigOpP(m,n,P,f) = Id
  BY DEF BigOpP, BigOp

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
<1> DEFINE Cf(i) == IF P(i) THEN f(i) ELSE Id  
<1>1. \A i \in m..n : Cf(i) \in D 
  BY OpIdentity  
<1> QED  
  BY <1>1, BigOpType DEF BigOpP

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
<1> DEFINE f(i) == Id
<1>        If(C,F1,F2) == IF C THEN F1 ELSE F2 
<1>E1. BigOpP(m,n,P,f) = BigOp(m,n,LAMBDA i : If(P(i),f(i),Id))  BY DEF BigOpP
<1>E2.              @  = BigOp(m,n,LAMBDA i : If(P(i),Id,Id))    OBVIOUS
<1>E3.              @  = BigOp(m,n,LAMBDA i : Id)                OBVIOUS
<1>E4.              @  = Id                                      BY OpIdentityExt
<1> QED
  BY <1>E1, <1>E2, <1>E3, <1>E4 

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
<1> DEFINE Cf(i) == IF P(i) THEN f(i) ELSE Id 
           Cg(i) == IF P(i) THEN g(i) ELSE Id 
<1> SUFFICES BigOp(m,n,Cf) = BigOp(m,n,Cg)
  BY DEF BigOpP 
<1>1. \A i \in m..n : Cf(i) \in D 
  BY OpIdentity
<1>2. \A i \in m..n : Cg(i) \in D
  BY OpIdentity  
<1>3. \A i \in m..n : Cf(i) = Cg(i)  
  OBVIOUS
<1> HIDE DEF Cf, Cg    
<1> QED 
  BY <1>1, <1>2, <1>3, FunctionEq, IsaM("blast") 

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
<1> DEFINE f1(i) == IF P(i) THEN f(i) ELSE Id
           f2(i) == Id
<1>1. \A i \in m..n : f1(i) \in D       BY OpIdentity 
<1>2. \A i \in m..n : f2(i) \in D       BY OpIdentity     
<1>3. \A i \in m..n : f1(i) = f2(i)     OBVIOUS
<1> HIDE DEF f1, f2
<1>E1. BigOpP(m,n,P,f) = BigOp(m,n,f1)    BY DEF f1, BigOpP
<1>E2.               @ = BigOp(m,n,f2)    BY <1>1, <1>2, <1>3, FunctionEq, IsaM("blast")
<1>E3.               @ = Id               BY OpIdentityExt DEF f2
<1> QED
  BY <1>E1, <1>E2, <1>E3

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
<1> DEFINE f1(i) == IF P(i) THEN f(i) ELSE Id
<1>1. \A i \in m..n : f1(i) \in D     BY OpIdentity   
<1>2. \A i \in m..n : f(i)  \in D     OBVIOUS
<1>3. \A i \in m..n : f1(i) = f(i)    OBVIOUS
<1> HIDE DEF f1
<1>E1. BigOpP(m,n,P,f) = BigOp(m,n,f1)    BY DEF f1, BigOpP
<1>E2.               @ = BigOp(m,n,f)     BY <1>1, <1>2, <1>3, FunctionEq, IsaM("blast")
<1> QED
  BY <1>E1, <1>E2

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
<1> DEFINE Cp(i) == IF P(i) THEN f(i) ELSE Id 
           Cq(i) == IF Q(i) THEN f(i) ELSE Id
<1> SUFFICES BigOp(m,n,Cp) = BigOp(m,n,Cq)
  BY DEF BigOpP 
<1>1. \A i \in m..n : Cp(i) \in D 
  BY OpIdentity
<1>2. \A i \in m..n : Cq(i) \in D
  BY OpIdentity
<1>3. \A i \in m..n : Cp(i) = Cq(i)
  OBVIOUS   
<1> HIDE DEF Cp, Cq     
<1> QED  
  BY <1>1, <1>2, <1>3, FunctionEq, IsaM("blast")
  
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
  BY UnitInterval DEF BigOpP
  
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
<1> DEFINE Cf(i) == IF P(i) THEN f(i) ELSE Id 
<1> SUFFICES BigOp(m,n,Cf) = BigOp(m,k,Cf) (\X) BigOp(k+1,n,Cf)
  BY DEF BigOpP 
<1>1. \A i \in m..n : Cf(i) \in D 
  BY OpIdentity  
<1> HIDE DEF Cf    
<1> QED 
  BY <1>1, SplitUp, IsaM("blast") 

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
         NEW k \in m..n,
         m <= n
  PROVE BigOpP(m,n,P,f) = BigOpP(m,k-1,P,f) (\X) BigOpP(k,n,P,f)     
<1> DEFINE Cf(i) == IF P(i) THEN f(i) ELSE Id 
<1> SUFFICES BigOp(m,n,Cf) = BigOp(m,k-1,Cf) (\X) BigOp(k,n,Cf)
  BY DEF BigOpP 
<1>1. \A i \in m..n : Cf(i) \in D 
  BY OpIdentity  
<1> HIDE DEF Cf    
<1> QED 
  BY <1>1, SplitDown, IsaM("blast")   

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
<1> DEFINE Cf(i) == IF P(i) THEN f(i) ELSE Id 
<1> SUFFICES BigOp(m,n,Cf) = Cf(m) (\X) BigOp(m+1,n,Cf)
  BY DEF BigOpP 
<1>1. \A i \in m..n : Cf(i) \in D 
  BY OpIdentity  
<1> HIDE DEF Cf    
<1> QED 
  BY <1>1, SplitFirst, IsaM("blast") 

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
<1> DEFINE Cf(i) == IF P(i) THEN f(i) ELSE Id 
<1> SUFFICES BigOp(m,n,Cf) = BigOp(m,n-1,Cf) (\X) Cf(n)
  BY DEF BigOpP 
<1>1. \A i \in m..n : Cf(i) \in D 
  BY OpIdentity  
<1> HIDE DEF Cf    
<1> QED 
  BY <1>1, SplitLast, IsaM("blast") 

=============================================================================
\* Modification History
\* Last modified Mon Aug 16 15:13:02 UYT 2021 by josedu
\* Last modified Sat Jun 26 14:17:23 GMT-03:00 2021 by JosEdu
\* Created Fri Jan 22 21:52:21 UYT 2021 by josedu
