------------------------ MODULE PCR_FibPrimes1_Lems ------------------------

EXTENDS PCR_FibPrimes1, ArithUtilsThms, TLAPS

USE DEF Index, Assig

LEMMA Lem_Type
  BY DEF Lem_Type, I0, T, lBnd, uBnd, prop, 
         pre, Dep_pp, Dep_pc, Dep_cr

LEMMA Lem_BFunWD
<1>0. SUFFICES ASSUME NEW x \in Nat, NEW i \in It(x)
               PROVE /\ gp(x,i) \in Tp
                     /\ \A vp \in St(Tp) : wrts(vp,deps(x,Dep_pp,i)\{i})
                          => fp(x,vp,i) \in Tp
                     /\ \A vp \in St(Tp) : wrts(vp,deps(x,Dep_pc,i))
                          => fc(x,vp,i) \in Tc
                     /\ \A vc \in St(Tc) : wrts(vc,deps(x,Dep_cr,i))
                          => fr(x,vc,i) \in D
  BY DEF Lem_BFunWD, T   
<1>1. /\ i \in Nat
      /\ It(x) \subseteq Nat
  BY DEF It, lBnd, uBnd, prop                   
<1>A. gp(x,i) \in Nat
  BY <1>1, fibonacciType DEF gp
<1>B. ASSUME NEW vp \in St(Nat), 
             wrts(vp,deps(x,Dep_pp,i)\{i}) 
      PROVE  fp(x,vp,i) \in Nat
  <2>A. CASE i <= 2
    BY <1>1, <2>A DEF fp, fibs 
  <2>B. CASE i > 2    
    <3>1. /\ i-1 \in deps(x,Dep_pp,i)\{i}
          /\ i-2 \in deps(x,Dep_pp,i)\{i}
      BY <1>1, <1>B, <2>B DEF deps, Dep_pp, lBnd, uBnd, prop 
    <3>2. wrt(vp[i-1]) /\ wrt(vp[i-2])
      BY <1>1, <1>B, <2>B, <3>1 DEF St, wrts
    <3>3. vp[i-1] \in Nat /\ vp[i-2] \in Nat 
      BY <1>1, <1>B, <2>B, <3>2 DEF It, St, wrt
    <3>4. fp(x,vp,i) \in Nat
      BY <3>3 DEF fp, fibs 
    <3> QED      
      BY <3>4  
  <2> QED
    BY <1>1, <2>A, <2>B     
<1>C. ASSUME NEW vp \in St(Nat), 
             wrts(vp,deps(x,Dep_pc,i)) 
      PROVE  fc(x,vp,i) \in BOOLEAN
  <2>1. wrt(vp[i])
    BY <1>C DEF St, wrts, deps    
  <2>2. vp[i] \in Nat
    BY <1>C, <1>1, <2>1 DEF It, St, wrt
  <2>3. fc(x,vp,i) \in BOOLEAN
    BY <2>2 DEF fc, isPrime
  <2> QED    
    BY <2>3
<1>D. ASSUME NEW vc \in St(BOOLEAN), 
             wrts(vc,deps(x,Dep_cr,i))
      PROVE  fr(x,vc,i) \in Nat
  <2>1. wrt(vc[i])
    BY <1>D DEF St, wrts, deps
  <2>2. vc[i] \in BOOLEAN
    BY <1>D, <1>1, <2>1 DEF It, St, wrt
  <2>3. fr(x,vc,i) \in Nat
    BY <2>2 DEF fr, toNat 
  <2> QED      
    BY <2>3
<1> QED     
  BY <1>A, <1>B, <1>C, <1>D DEF Tp, Tc, D           

LEMMA Lem_fpRelevance
<1>0. SUFFICES ASSUME NEW x \in Nat, NEW i \in It(x), 
                      NEW vp1 \in St(Nat), NEW vp2 \in St(Nat),
                      eqs(vp1,vp2,deps(x,Dep_pp,i)\{i})
               PROVE  fp(x,vp1,i) = fp(x,vp2,i)
  BY DEF Lem_fpRelevance, T, Tp 
<1>1. /\ i \in Nat
      /\ It(x) \subseteq Nat
  BY DEF It, lBnd, uBnd, prop  
<1>A. CASE i <= 2  
  BY <1>1, <1>A DEF fp, fibs
<1>B. CASE i > 2  
  <2>1. /\ wrt(vp1[i-1]) /\ wrt(vp1[i-2]) 
        /\ wrt(vp2[i-1]) /\ wrt(vp2[i-2]) 
        /\ vp1[i-1] = vp2[i-1]
        /\ vp1[i-2] = vp2[i-2]
    <3>1. /\ i-1 \in deps(x,Dep_pp,i)\{i} 
          /\ i-2 \in deps(x,Dep_pp,i)\{i}
      BY <1>1, <1>B DEF deps, Dep_pp, lBnd, uBnd, prop
    <3> QED      
      BY <1>0, <1>1, <3>1 DEF St, eqs
  <2>2. /\ vp1[i-1] \in Nat /\ vp1[i-2] \in Nat
        /\ vp2[i-1] \in Nat /\ vp2[i-2] \in Nat
    BY <1>0, <1>B, <1>1, <2>1 DEF It, St, wrt
  <2>3. fp(x,vp1,i) = fp(x,vp2,i)
    BY <1>1, <1>B, <2>1, <2>2 DEF fp, fibs
  <2> QED
    BY <2>3
<1> QED  
  BY <1>1, <1>A, <1>B

LEMMA Lem_fcRelevance
<1>0. SUFFICES ASSUME NEW x \in Nat, NEW i \in It(x), 
                      NEW vp1 \in St(Nat), NEW vp2 \in St(Nat),
                      eqs(vp1,vp2,deps(x,Dep_pc,i))
               PROVE  fc(x,vp1,i) = fc(x,vp2,i)
  BY DEF Lem_fcRelevance, T, Tp 
<1>1. /\ i \in Nat
      /\ It(x) \subseteq Nat
  BY DEF It, lBnd, uBnd, prop 
<1>2. /\ wrt(vp1[i])
      /\ wrt(vp2[i])
      /\ vp1[i] = vp2[i]
  BY <1>0 DEF St, eqs, deps
<1>3. /\ vp1[i] \in Nat
      /\ vp2[i] \in Nat
  BY <1>1, <1>2 DEF It, St, wrt
<1>4. fc(x,vp1,i) = fc(x,vp2,i)
  BY <1>2, <1>3 DEF fc, isPrime
<1> QED 
  BY <1>4 

LEMMA Lem_frRelevance
<1>0. SUFFICES ASSUME NEW x \in Nat, NEW i \in It(x), 
                      NEW vc1 \in St(BOOLEAN), NEW vc2 \in St(BOOLEAN),
                      eqs(vc1,vc2,deps(x,Dep_cr,i))
               PROVE  fr(x,vc1,i) = fr(x,vc2,i)
  BY DEF Lem_frRelevance, T, Tc 
<1>1. /\ i \in Nat
      /\ It(x) \subseteq Nat
  BY DEF It, lBnd, uBnd, prop  
<1>2. /\ wrt(vc1[i])
      /\ wrt(vc2[i])
      /\ vc1[i] = vc2[i]
  BY <1>0 DEF St, eqs, deps
<1>3. /\ vc1[i] \in BOOLEAN
      /\ vc2[i] \in BOOLEAN
  BY <1>1, <1>2 DEF It, St, wrt
<1>4. fr(x,vc1,i) = fr(x,vc2,i)
  BY <1>2, <1>3 DEF fr, toNat
<1> QED  
  BY <1>4  

LEMMA Lem_Algebra
<1>0. SUFFICES /\ \A x, y \in Nat : x + y \in Nat
               /\ \A x, y, z \in Nat : (x + y) + z = x + (y + z)
               /\ \A x \in Nat : x + 0 = x /\ 0 + x = x
               /\ \A x, y \in Nat : x + y = y + x
  BY DEF Lem_Algebra, D, id, Op, AbelianMonoid, Monoid, SemiGroup, Magma     
<1> QED
  BY SMT

============================================================================
\* Modification History
\* Last modified Wed Sep 08 18:42:19 UYT 2021 by josedu
\* Last modified Tue Jul 06 15:39:14 GMT-03:00 2021 by JosEdu
\* Created Mon Jul 05 18:48:36 GMT-03:00 2021 by JosEdu
