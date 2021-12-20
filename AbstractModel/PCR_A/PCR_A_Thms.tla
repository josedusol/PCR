----------------------------- MODULE PCR_A_Thms -----------------------------

EXTENDS PCR_A, TLAPS

USE DEF Index, Assig, red

MT == INSTANCE AbelianMonoidBigOpThms
  WITH D <- D, Id <- id, \otimes <- Op 

LEMMA H_AMon == /\ MT!Monoid(D, id, Op)
                /\ \A x, y \in D : Op(x, y) = Op(y, x)
  BY H_Algebra DEF AbelianMonoid, MT!AbelianMonoid,
                   Monoid,        MT!Monoid, 
                   SemiGroup,     MT!SemiGroup,
                   Magma,         MT!Magma
                   
LEMMA H_MeqMT == ASSUME NEW x, NEW y, NEW Q(_), NEW f(_)
                 PROVE /\ M!BigOp(x,y,f)    = MT!BigOp(x,y,f)
                       /\ M!BigOpP(x,y,Q,f) = MT!BigOpP(x,y,Q,f)
  BY DEF M!BigOpP, MT!BigOpP, 
         M!BigOp,  MT!BigOp,
         M!bigOp,  MT!bigOp                  

LEMMA H_Undef == Undef \notin UNION {T, Tp, Tc, D} 
  BY NoSetContainsEverything DEF Undef

THEOREM Thm_IndexInv == Spec => []IndexInv
<1>1. Init => IndexInv
  BY H_Type, H_Undef DEF Init, IndexInv, WDIndex, wrt
<1>2. /\ IndexInv 
      /\ [Next]_<<in,vs>>
      => IndexInv'
  <2>0. SUFFICES ASSUME IndexInv,
                        [Next]_<<in,vs>>
                 PROVE  IndexInv'
    OBVIOUS
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E I \in WDIndex : 
                            \E i \in It(X[I]) : \/ P(I,i) 
                                                \/ C(I,i)
                                                \/ R(I,i)
                   PROVE IndexInv'
      BY <2>0, <2>A DEF Step
    <3>1. PICK I \in WDIndex :
                 \E i \in It(X[I]) : \/ P(I,i) 
                                     \/ C(I,i)
                                     \/ R(I,i)
      BY <3>0             
    <3>2. PICK i \in It(X[I]) : \/ P(I,i) 
                                \/ C(I,i)
                                \/ R(I,i)
      BY <3>1  
    <3>A. CASE P(I,i)    
      <4>0. SUFFICES ASSUME P(I,i)
                     PROVE  WDIndex = { I0 }
         BY <2>0, <3>A DEF P, IndexInv, WDIndex   
      <4>1. WDIndex = { I0 }
        BY <2>0 DEF IndexInv                 
      <4> QED 
        BY <4>1              
    <3>B. CASE C(I,i)
      <4>0. SUFFICES ASSUME C(I,i)
                     PROVE  WDIndex = { I0 }
        BY <2>0, <3>B DEF C, IndexInv, WDIndex    
      <4>1. WDIndex = { I0 }
        BY <2>0 DEF IndexInv                 
      <4> QED 
        BY <4>1      
    <3>C. CASE R(I,i)     
      <4>0. SUFFICES ASSUME R(I,i)
                     PROVE  WDIndex = { I0 }
        BY <2>0, <3>C DEF R, IndexInv, WDIndex
      <4>1. WDIndex = { I0 }
        BY <2>0 DEF IndexInv                 
      <4> QED 
        BY <4>1       
    <3> QED
      BY <3>2, <3>A, <3>B, <3>C         
  <2>B. CASE Done  
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>
                   PROVE  WDIndex = { I0 }
      BY <2>0, <2>B DEF Done, vs, IndexInv, WDIndex
    <3>1. WDIndex = { I0 }
      BY <2>0 DEF IndexInv
    <3> QED
      BY <3>1
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>
                   PROVE  WDIndex = { I0 }
      BY <2>0, <2>C DEF vs, IndexInv, WDIndex
    <3>1. WDIndex = { I0 }
      BY <2>0 DEF IndexInv
    <3> QED
      BY <3>1  
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next            
<1> QED      
  BY <1>1, <1>2, PTL DEF Spec 

THEOREM Thm_TypeInv == Spec => []TypeInv
<1> DEFINE x == X[I0]
           m == lBnd(X[I0]) 
           n == uBnd(X[I0])
<1>1. Init => TypeInv
  <2> SUFFICES ASSUME Init
               PROVE  TypeInv
    OBVIOUS
  <2>1. /\ in \in T
        /\ X  \in [Index -> T \union {Undef}] /\ X[I0] = in
        /\ p  \in [Index -> St(Tp)]  
        /\ c  \in [Index -> St(Tc)]
        /\ rs \in [Index -> [Nat -> BOOLEAN]]              
    BY H_Type DEF Init, St     
  <2>2. r \in [Index -> D]
    BY H_Algebra DEF Init, AbelianMonoid, Monoid 
  <2> QED 
    BY <2>1, <2>2 DEF TypeInv
<1>2. /\ IndexInv
      /\ TypeInv 
      /\ [Next]_<<in,vs>>
      => TypeInv'
  <2>0. SUFFICES ASSUME IndexInv,
                        TypeInv,
                        [Next]_<<in,vs>>
                 PROVE  TypeInv'
    OBVIOUS
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i)
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE  TypeInv'
      BY <2>0, <2>A, H_Type DEF Step, IndexInv
    <3>1. PICK i \in It(x) : \/ P(I0,i)
                             \/ C(I0,i)
                             \/ R(I0,i)
      BY <3>0 
    <3>2. x \in T
      BY <2>0 DEF IndexInv, TypeInv, WDIndex, wrt
    <3>3. /\ I0 \in Seq(Nat) 
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in {k \in m..n : prop(k)}
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It 
    <3>4. in' = in
      BY <2>A DEF Step     
      
    <3>A. CASE P(I0,i) 
      <4>1. /\ in' \in T
            /\ X'  \in [Index -> T \union {Undef}] /\ X[I0]' = in'
            /\ c'  \in [Index -> St(Tc)]
            /\ r'  \in [Index -> D] 
            /\ rs' \in [Index -> [Nat -> BOOLEAN]]  
        <5>1. <<in,X,c,r,rs>>' = <<in,X,c,r,rs>> 
          BY <3>4, <3>A DEF P
        <5> QED 
          BY <2>0, <5>1 DEF TypeInv            
      <4>2. p' \in [Index -> St(Tp)]
        <5>1. /\ wrts(p[I0],deps(x,Dep_pp,i)\{i})
              /\ p' = [p EXCEPT ![I0][i] = fp(x,p[I0],i)]
          BY <3>A DEF P 
        <5>2. p \in [Index -> St(Tp)]    
          BY <2>0 DEF TypeInv 
        <5>3. fp(x,p[I0],i) \in Tp  
          BY <2>0, <3>2, <3>3, <5>1, <5>2, H_BFunWD
        <5>5. p[I0][i]' \in Tp \union {Undef}
          BY <3>3, <5>1, <5>2, <5>3 DEF St
        <5> QED 
          BY <5>1, <5>2, <5>5 DEF St      
      <4> QED
        BY <4>1, <4>2 DEF TypeInv      
           
    <3>B. CASE C(I0,i)
      <4>1. /\ in' \in T
            /\ X'  \in [Index -> T \union {Undef}] /\ X[I0]' = in'
            /\ p'  \in [Index -> St(Tp)]
            /\ r'  \in [Index -> D] 
            /\ rs' \in [Index -> [Nat -> BOOLEAN]]              
        <5>1. <<in,X,p,r,rs>>' = <<in,X,p,r,rs>> 
          BY <3>4, <3>B DEF C
        <5> QED 
          BY <2>0, <5>1 DEF TypeInv            
      <4>2. c' \in [Index -> St(Tc)]
        <5>1. /\ wrts(p[I0],deps(x,Dep_pc,i))
              /\ c' = [c EXCEPT ![I0][i] = fc(x,p[I0],i)]
          BY <3>B DEF C 
        <5>2. /\ c \in [Index -> St(Tc)]   
              /\ p \in [Index -> St(Tp)]    
          BY <2>0 DEF TypeInv          
        <5>3. fc(x,p[I0],i) \in Tc
          BY <2>0, <3>2, <3>3, <5>2, <5>1, H_BFunWD
        <5>5. c[I0][i]' \in Tc \union {Undef}
          BY <3>3, <5>1, <5>2, <5>3 DEF St
        <5> QED 
          BY <5>1, <5>2, <5>5 DEF St      
      <4> QED
        BY <4>1, <4>2 DEF TypeInv    
         
    <3>C. CASE R(I0,i) 
      <4>1. /\ in'\in T
            /\ X' \in [Index -> T \union {Undef}] /\ X[I0]' = in'
            /\ c' \in [Index -> St(Tc)]
            /\ p' \in [Index -> St(Tp)]
        <5>1. <<in,X,p,c>>' = <<in,X,p,c>> 
          BY <3>4, <3>C DEF R
        <5> QED 
          BY <2>0, <5>1 DEF TypeInv    
      <4>2. /\ wrts(c[I0],deps(x,Dep_cr,i))
            /\ r'  = [r  EXCEPT ![I0]    = Op(@, fr(x,c[I0],i))]
            /\ rs' = [rs EXCEPT ![I0][i] = TRUE]
        BY <3>C DEF R     
      <4>3. /\ c  \in [Index -> St(Tc)]
            /\ rs \in [Index -> [Nat -> BOOLEAN]] 
            /\ r  \in [Index -> D]
        BY <2>0 DEF TypeInv                  
      <4>4. r' \in [Index -> D]  
        <5>1. r[I0] \in D
          BY <2>0, <3>3 DEF TypeInv
        <5>2. fr(x,c[I0],i) \in D
          BY <2>0, <3>2, <3>3, <4>2, <4>3, H_BFunWD    
        <5>3. Op(r[I0], fr(x,c[I0],i)) \in D
          BY <5>1, <5>2, H_Algebra 
          DEF AbelianMonoid, Monoid, SemiGroup, Magma
        <5>6. r[I0]' \in D
          BY <3>3, <4>2, <4>3, <5>3 DEF St  
        <5> QED     
          BY <4>2, <4>3, <5>6         
      <4>5. rs' \in [Index -> [Nat -> BOOLEAN]]
        BY <4>2, <4>3
      <4> QED    
        BY <4>1, <4>4, <4>5 DEF TypeInv    
             
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C
  <2>B. CASE Done
    <3>1. <<in,X,p,c,r,rs>>' = <<in,X,p,c,r,rs>> 
      BY <2>B DEF Done, vs
    <3> QED
      BY <3>1, <2>0 DEF TypeInv     
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>1. <<in,X,p,c,r,rs>>' = <<in,X,p,c,r,rs>> 
      BY <2>C DEF vs
    <3> QED
      BY <3>1, <2>0 DEF TypeInv 
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next   
<1> QED 
  BY <1>1, <1>2, Thm_IndexInv, PTL DEF Spec 

THEOREM Thm_PInv == Spec => []PInv
<1> DEFINE x == X[I0]
           m == lBnd(X[I0]) 
           n == uBnd(X[I0])
<1>1. Init => PInv
  <2>0. SUFFICES ASSUME Init,
                        NEW i \in It(x),
                        wrt(p[I0][i])
                 PROVE  FALSE
    BY DEF PInv
  <2>1. /\ I0    \in Seq(Nat) 
        /\ x     \in T        
        /\ It(x) \subseteq Nat
    BY <2>0, H_Type DEF Init, It         
  <2>2. ~ wrt(p[I0][i])  
    BY <2>0, <2>1 DEF Init, wrt   
  <2>3. FALSE    
    BY <2>0, <2>2   
  <2> QED  
    BY <2>3
<1>2. /\ IndexInv /\ TypeInv /\ TypeInv' 
      /\ PInv 
      /\ [Next]_<<in,vs>>
      => PInv'
  <2>0. SUFFICES ASSUME IndexInv, TypeInv, TypeInv',
                        PInv,
                        [Next]_<<in,vs>>
                 PROVE  PInv'
    OBVIOUS
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i) 
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE PInv'
      BY <2>0, <2>A DEF Step, IndexInv    
    <3>1. PICK i \in It(x) : \/ P(I0,i) 
                             \/ C(I0,i)
                             \/ R(I0,i)
      BY <3>0 
    <3>2. x \in T
      BY <2>0 DEF IndexInv, TypeInv, WDIndex, wrt
    <3>3. /\ I0 \in Seq(Nat) 
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in {k \in m..n : prop(k)} 
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It       
    <3>4. m \in Nat /\ n \in Nat 
      BY <2>0, <3>2, H_Type DEF TypeInv, m, n 
          
    <3>A. CASE P(I0,i)    
      <4>0. SUFFICES ASSUME P(I0,i),
                            NEW j \in It(x),
                            wrt(p[I0][j])'
                     PROVE  /\ p[I0][j]' = fp(x,p[I0]',j)
                            /\ wrts(p[I0]',deps(x,Dep_pp,j))
         BY <2>0, <3>A DEF P, PInv, It     
      <4>1. /\ ~ wrt(p[I0][i])
            /\ wrts(p[I0],deps(x,Dep_pp,i)\{i})
            /\ p' = [p EXCEPT ![I0][i] = fp(x,p[I0],i)] 
            /\ X' = X
        BY <4>0 DEF P  
      <4>2. \A k \in It(x) : k # i => p[I0][k]' = p[I0][k]
        BY <4>1
      <4>A. CASE i = j 
        <5>1. p[I0][i]' = fp(x,p[I0],i)   
          BY <2>0, <3>3, <4>1 DEF TypeInv, St 
        <5>2. fp(x,p[I0],i) \in Tp  
          BY <2>0, <3>2, <3>3, <4>1, H_BFunWD DEF TypeInv       
        <5>3. wrt(p[I0][i])'
          BY <5>1, <5>2, H_Undef DEF wrt          
        <5>4. /\ eqs(p[I0],p[I0]',deps(x,Dep_pp,i)\{i})   
              /\ p[I0] \in St(Tp) /\ p[I0]' \in St(Tp)
          <6>1. wrts(p[I0],deps(x,Dep_pp,i)\{i})
            BY <4>1
          <6>2. deps(x,Dep_pp,i)\{i} \subseteq It(x)  
            BY <3>2, <3>3, H_Type DEF deps, It
          <6>3. i \notin deps(x,Dep_pp,i)\{i}
            OBVIOUS
          <6>4. \A k \in deps(x,Dep_pp,i)\{i} : 
                  wrt(p[I0][k]) /\ p[I0][k] = p[I0]'[k]
            BY <4>2, <6>1, <6>2, <6>3 DEF wrts         
          <6>5. p[I0] \in St(Tp) /\ p[I0]' \in St(Tp)
            BY <2>0, <3>3 DEF TypeInv, St
          <6> QED  
            BY <6>4, <6>5 DEF eqs              
        <5>5. fp(x,p[I0],i) = fp(x,p[I0]',i)
          BY <3>2, <3>3, <5>4, H_fpRelevance 
        <5>6. wrts(p[I0]',deps(x,Dep_pp,i))
          BY <5>3, <5>4 DEF eqs, wrts
        <5>7. /\ p[I0][i]' = fp(x,p[I0]',i)
              /\ wrts(p[I0]',deps(x,Dep_pp,i))       
          BY <5>1, <5>5, <5>6       
        <5> QED 
          BY <4>A, <5>7   
      <4>B. CASE i # j            
        <5>1. p[I0][j]' = p[I0][j]  
          BY <4>2, <4>B 
        <5>2. wrt(p[I0][j])    
          BY <4>0, <5>1 DEF wrt     
        <5>3. /\ p[I0][j] = fp(x,p[I0],j)
              /\ wrts(p[I0],deps(x,Dep_pp,j))
          BY <2>0, <5>2 DEF PInv
        <5>4. /\ eqs(p[I0],p[I0]',deps(x,Dep_pp,j)\{j})   
              /\ p[I0] \in St(Tp) /\ p[I0]' \in St(Tp)
          <6>1. wrts(p[I0],deps(x,Dep_pp,j)\{j})
            BY <5>3 DEF wrts, deps
          <6>2. deps(x,Dep_pp,j)\{j} \subseteq It(x)  
            BY <3>2, <3>3, H_Type DEF deps, It
          <6>3. i \notin deps(x,Dep_pp,j)\{j}
            BY <4>B, <4>1, <5>3 DEF wrts  
          <6>4. \A k \in deps(x,Dep_pp,j)\{j} : 
                  wrt(p[I0][k]) /\ p[I0][k] = p[I0]'[k]
            BY <4>2, <6>1, <6>2, <6>3 DEF wrts         
          <6>5. p[I0] \in St(Tp) /\ p[I0]' \in St(Tp)
            BY <2>0, <3>3 DEF TypeInv, St
          <6> QED  
            BY <6>4, <6>5 DEF eqs               
        <5>5. fp(x,p[I0],j) = fp(x,p[I0]',j)
          BY <3>2, <3>3, <5>4, H_fpRelevance          
        <5>6. wrts(p[I0]',deps(x,Dep_pp,j))
          BY <4>0, <5>4 DEF eqs, wrts    
        <5>7. /\ p[I0][j]' = fp(x,p[I0]',j)
              /\ wrts(p[I0]',deps(x,Dep_pp,j))       
          BY <5>1, <5>3, <5>5, <5>6       
        <5> QED
          BY <5>7    
      <4> QED 
        BY <4>A, <4>B  
                      
    <3>B. CASE C(I0,i)
      <4>0. SUFFICES ASSUME C(I0,i),
                            NEW j \in It(x),
                            wrt(p[I0][j])
                     PROVE  /\ p[I0][j] = fp(x,p[I0],j)
                            /\ wrts(p[I0],deps(x,Dep_pp,j))
        BY <2>0, <3>B DEF C, PInv, It     
      <4>1. /\ p[I0][j] = fp(x,p[I0],j)
            /\ wrts(p[I0],deps(x,Dep_pp,j))  
        BY <2>0, <4>0 DEF PInv               
      <4> QED 
        BY <4>1
                 
    <3>C. CASE R(I0,i)     
      <4>0. SUFFICES ASSUME R(I0,i),
                            NEW j \in It(x),
                            wrt(p[I0][j])
                     PROVE  /\ p[I0][j] = fp(x,p[I0],j)
                            /\ wrts(p[I0],deps(x,Dep_pp,j))
        BY <2>0, <3>C DEF R, PInv, It     
      <4>1. /\ p[I0][j] = fp(x,p[I0],j)
            /\ wrts(p[I0],deps(x,Dep_pp,j))  
        BY <2>0, <4>0 DEF PInv               
      <4> QED 
        BY <4>1  
                
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C              
  <2>B. CASE Done  
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x),
                          wrt(p[I0][i])
                   PROVE  /\ p[I0][i] = fp(x,p[I0],i)
                          /\ wrts(p[I0],deps(x,Dep_pp,i))
      BY <2>0, <2>B DEF Done, vs, PInv, It
    <3>1. /\ p[I0][i] = fp(x,p[I0],i)
          /\ wrts(p[I0],deps(x,Dep_pp,i))   
      BY <2>0, <3>0 DEF PInv
    <3> QED
      BY <3>1
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x),
                          wrt(p[I0][i])
                   PROVE  /\ p[I0][i] = fp(x,p[I0],i)
                          /\ wrts(p[I0],deps(x,Dep_pp,i))
      BY <2>0, <2>C DEF vs, PInv, It
    <3>1. /\ p[I0][i] = fp(x,p[I0],i)
          /\ wrts(p[I0],deps(x,Dep_pp,i))   
      BY <2>0, <3>0 DEF PInv
    <3> QED
      BY <3>1    
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next            
<1> QED      
  BY <1>1, <1>2, Thm_IndexInv, Thm_TypeInv, PTL DEF Spec 
  
THEOREM Thm_CInv == Spec => []CInv
<1> DEFINE x == X[I0]
           m == lBnd(X[I0]) 
           n == uBnd(X[I0])
<1>1. Init => CInv
  <2>0. SUFFICES ASSUME Init,
                        NEW i \in It(x),
                        wrt(c[I0][i])
                 PROVE  FALSE
    BY DEF CInv
  <2>1. /\ I0    \in Seq(Nat) 
        /\ x     \in T        
        /\ It(x) \subseteq Nat
    BY <2>0, H_Type DEF Init, It         
  <2>2. ~ wrt(c[I0][i])  
    BY <2>0, <2>1 DEF Init, wrt   
  <2>3. FALSE    
    BY <2>0, <2>2   
  <2> QED  
    BY <2>3
<1>2. /\ IndexInv /\ TypeInv /\ TypeInv'
      /\ CInv 
      /\ [Next]_<<in,vs>>
      => CInv'
  <2>0. SUFFICES ASSUME IndexInv, TypeInv, TypeInv',
                        CInv,
                        [Next]_<<in,vs>>
                 PROVE  CInv'
    OBVIOUS
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i)
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE CInv'
      BY <2>0, <2>A DEF Step, IndexInv    
    <3>1. PICK i \in It(x) : \/ P(I0,i)
                             \/ C(I0,i)
                             \/ R(I0,i)
      BY <3>0 
    <3>2. x \in T
      BY <2>0 DEF IndexInv, TypeInv, WDIndex, wrt   
    <3>3. /\ I0 \in Seq(Nat)
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in {k \in m..n : prop(k)}
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It       
    <3>4. m \in Nat /\ n \in Nat 
      BY <2>0, <3>2, H_Type DEF TypeInv, m, n     
           
    <3>A. CASE P(I0,i)    
      <4>0. SUFFICES ASSUME P(I0,i),
                            NEW j \in It(x),
                            wrt(c[I0][j])
                     PROVE  /\ c[I0][j] = fc(x,p[I0]',j)
                            /\ wrts(p[I0]',deps(x,Dep_pc,j))
        BY <2>0, <3>A DEF P, CInv, It  
      <4>1. /\ ~ wrt(p[I0][i])
            /\ p' = [p EXCEPT ![I0][i] = fp(x,p[I0],i)] 
            /\ <<X,c>>' = <<X,c>>
        BY <4>0 DEF P         
      <4>2. \A k \in It(x) : k # i => p[I0]'[k] = p[I0][k]
        BY <4>1    
      <4>3. /\ c[I0][j]  = fc(x,p[I0],j)
            /\ wrts(p[I0],deps(x,Dep_pc,j))
        BY <2>0, <4>0 DEF CInv           
      <4>4. /\ eqs(p[I0],p[I0]',deps(x,Dep_pc,j))   
            /\ p[I0] \in St(Tp) /\ p[I0]' \in St(Tp)        
        <5>1. deps(x,Dep_pc,j) \subseteq It(x)
          BY <3>2, <3>3, H_Type DEF deps,It                      
        <5>2. i \notin deps(x,Dep_pc,j)
          BY <4>1, <4>3 DEF wrts           
        <5>3. \A k \in deps(x,Dep_pc,j) :
                wrt(p[I0][k]) /\ p[I0][k] = p[I0]'[k]
          BY <4>2, <4>3, <5>1, <5>2 DEF wrts         
        <5>4. p[I0] \in St(Tp) /\ p[I0]' \in St(Tp)
          BY <2>0, <3>3 DEF TypeInv, St  
        <5> QED
          BY <5>3, <5>4 DEF eqs                         
      <4>5. wrts(p[I0]',deps(x,Dep_pc,j))
        BY <4>2, <4>3, <4>4 DEF wrts, eqs      
      <4>E1. c[I0][j]  = fc(x,p[I0],j)    BY <4>3  
      <4>E2.         @ = fc(x,p[I0]',j)   BY <3>2, <3>3, <4>4, H_fcRelevance                                               
      <4> QED 
        BY <4>5, <4>E1, <4>E2
                       
    <3>B. CASE C(I0,i)
      <4>0. SUFFICES ASSUME C(I0,i),
                            NEW j \in It(x),
                            wrt(c[I0][j])'
                     PROVE  /\ c[I0][j]' = fc(x,p[I0],j)
                            /\ wrts(p[I0],deps(x,Dep_pc,j))
        BY <2>0, <3>B DEF C, CInv, It     
      <4>1. /\ ~ wrt(c[I0][i])
            /\ wrts(p[I0],deps(x,Dep_pc,i))
            /\ c' = [c EXCEPT ![I0][i] = fc(x,p[I0],i)] 
            /\ <<X,p>>' = <<X,p>>
        BY <4>0 DEF C        
      <4>A. CASE i = j
        <5>1. c[I0][i]' = fc(x,p[I0],i)
          BY <2>0, <3>3, <4>1, <4>A DEF TypeInv, St     
        <5>2. wrts(p[I0],deps(x,Dep_pc,i))
          BY <4>1
        <5> QED 
          BY <4>A, <5>1, <5>2         
      <4>B. CASE i # j            
        <5>1. \A k \in It(x) : k # i => c[I0][k]' = c[I0][k]
          BY <4>1
        <5>2. c[I0][j]' = c[I0][j]  
          BY <4>B, <5>1
        <5>3. wrt(c[I0][j])    
          BY <4>0, <5>2 DEF wrt     
        <5>4. /\ c[I0][j] = fc(x,p[I0],j)
              /\ wrts(p[I0],deps(x,Dep_pc,j))
          BY <2>0, <5>3 DEF CInv    
        <5> QED
          BY <5>2, <5>4       
      <4> QED 
        BY <4>A, <4>B         
                          
    <3>C. CASE R(I0,i)     
      <4>0. SUFFICES ASSUME R(I0,i),
                            NEW j \in It(x),
                            wrt(c[I0][j])
                     PROVE  /\ c[I0][j] = fc(x,p[I0],j)
                            /\ wrts(p[I0],deps(x,Dep_pc,j))
        BY <2>0, <3>C DEF R, CInv, It     
      <4>1. /\ c[I0][j] = fc(x,p[I0],j) 
            /\ wrts(p[I0],deps(x,Dep_pc,j))  
        BY <2>0, <4>0 DEF CInv               
      <4> QED 
        BY <4>1   
          
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C             
  <2>B. CASE Done  
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x),
                          wrt(c[I0][i])
                   PROVE  /\ c[I0][i] = fc(x,p[I0],i)
                          /\ wrts(p[I0],deps(x,Dep_pc,i))
      BY <2>0, <2>B DEF Done, vs, CInv, It
    <3>1. /\ c[I0][i] = fc(x,p[I0],i)   
          /\ wrts(p[I0],deps(x,Dep_pc,i))  
      BY <2>0, <3>0 DEF CInv
    <3> QED
      BY <3>1   
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x),
                          wrt(c[I0][i])
                   PROVE  /\ c[I0][i] = fc(x,p[I0],i)
                          /\ wrts(p[I0],deps(x,Dep_pc,i))
      BY <2>0, <2>C DEF vs, CInv, It
    <3>1. /\ c[I0][i] = fc(x,p[I0],i)   
          /\ wrts(p[I0],deps(x,Dep_pc,i))  
      BY <2>0, <3>0 DEF CInv
    <3> QED
      BY <3>1        
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next            
<1> QED      
  BY <1>1, <1>2, Thm_IndexInv, Thm_TypeInv, PTL DEF Spec 

THEOREM Thm_RInv1 == Spec => []RInv1
<1> DEFINE x == X[I0]
           m == lBnd(X[I0]) 
           n == uBnd(X[I0])
<1>1. Init => RInv1
  <2>0. SUFFICES ASSUME Init,
                        NEW i \in It(x),
                        red(I0,i)
                 PROVE  FALSE
    BY DEF RInv1
  <2>1. /\ I0    \in Seq(Nat) 
        /\ x     \in T        
        /\ It(x) \subseteq Nat
    BY <2>0, H_Type DEF Init, It         
  <2>2. ~ red(I0,i)  
    BY <2>0, <2>1 DEF Init, wrt   
  <2>3. FALSE    
    BY <2>0, <2>2   
  <2> QED  
    BY <2>3
<1>2. /\ IndexInv /\ TypeInv /\ TypeInv'
      /\ RInv1 
      /\ [Next]_<<in,vs>>
      => RInv1'
  <2>0. SUFFICES ASSUME IndexInv, TypeInv, TypeInv',
                        RInv1,
                        [Next]_<<in,vs>>
                 PROVE  RInv1'
    OBVIOUS
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i)
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE RInv1'
      BY <2>0, <2>A DEF Step, IndexInv    
    <3>1. PICK i \in It(x) : \/ P(I0,i)
                             \/ C(I0,i)
                             \/ R(I0,i)
      BY <3>0 
    <3>2. x \in T
      BY <2>0 DEF IndexInv, TypeInv, WDIndex, wrt   
    <3>3. /\ I0 \in Seq(Nat)
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in {k \in m..n : prop(k)}
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It       
    <3>4. m \in Nat /\ n \in Nat 
      BY <2>0, <3>2, H_Type DEF TypeInv, m, n     
           
    <3>A. CASE P(I0,i)    
      <4>0. SUFFICES ASSUME P(I0,i),
                            NEW j \in It(x),
                            red(I0,j)
                     PROVE  wrts(c[I0],deps(x,Dep_cr,j))
        BY <2>0, <3>A DEF P, RInv1, It  
      <4>1. wrts(c[I0],deps(x,Dep_cr,j)) 
        BY <2>0, <4>0 DEF RInv1                                               
      <4> QED 
        BY <4>1
                       
    <3>B. CASE C(I0,i)
      <4>0. SUFFICES ASSUME C(I0,i),
                            NEW j \in It(x),
                            red(I0,j)
                     PROVE  wrts(c[I0]',deps(x,Dep_cr,j))
        BY <2>0, <3>B DEF C, RInv1, It     
      <4>1. /\ ~ wrt(c[I0][i])
            /\ wrts(p[I0],deps(x,Dep_pc,i))
            /\ c' = [c EXCEPT ![I0][i] = fc(x,p[I0],i)] 
            /\ <<X,p>>' = <<X,p>>
        BY <4>0 DEF C        
      <4>2. \A k \in It(x) : k # i => c[I0]'[k] = c[I0][k]
        BY <4>1   
      <4>3. wrts(c[I0],deps(x,Dep_cr,j))  
        BY <2>0, <4>0 DEF RInv1   
      <4>4. deps(x,Dep_cr,j) \subseteq It(x)
        BY <3>2, <3>3, H_Type DEF deps,It                      
      <4>5. i \notin deps(x,Dep_cr,j)
        BY <4>1, <4>3 DEF wrts              
      <4>6. wrts(c[I0]',deps(x,Dep_cr,j))
        BY <4>2, <4>3, <4>4, <4>5 DEF wrts           
      <4> QED   
        BY <4>6   
                          
    <3>C. CASE R(I0,i)     
      <4>0. SUFFICES ASSUME R(I0,i),
                            NEW j \in It(x),
                            red(I0,j)'
                     PROVE  wrts(c[I0],deps(x,Dep_cr,j))
        BY <2>0, <3>C DEF R, RInv1, It     
      <4>1. /\ ~ red(I0,i)    
            /\ wrts(c[I0],deps(x,Dep_cr,i))
            /\ rs' = [rs EXCEPT ![I0][i] = TRUE]
            /\ <<X,c>>' = <<X,c>>            
        BY <4>0 DEF R  
      <4>A. CASE i = j    
        <5>1. wrts(c[I0],deps(x,Dep_cr,i))
          BY <4>1
        <5> QED 
          BY <4>A, <5>1         
      <4>B. CASE i # j            
        <5>1. \A k \in It(x) : k # i => red(I0,k)' = red(I0,k)
          BY <4>1
        <5>2. red(I0,j)'
          BY <4>0, <4>B, <5>1
        <5>3. red(I0,j)    
          BY <4>B, <5>1, <5>2   
        <5>4. wrts(c[I0],deps(x,Dep_cr,j))
          BY <2>0, <5>3 DEF RInv1    
        <5> QED
          BY <5>4       
      <4> QED 
        BY <4>A, <4>B 
           
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C             
  <2>B. CASE Done  
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x),
                          red(I0,i)
                   PROVE  wrts(c[I0],deps(x,Dep_cr,i))
      BY <2>0, <2>B DEF Done, vs, RInv1, It
    <3>1. wrts(c[I0],deps(x,Dep_cr,i))
      BY <2>0, <3>0 DEF RInv1
    <3> QED
      BY <3>1   
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x),
                          red(I0,i)
                   PROVE  wrts(c[I0],deps(x,Dep_cr,i))
      BY <2>0, <2>C DEF vs, RInv1, It
    <3>1. wrts(c[I0],deps(x,Dep_cr,i)) 
      BY <2>0, <3>0 DEF RInv1
    <3> QED
      BY <3>1        
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next            
<1> QED      
  BY <1>1, <1>2, Thm_IndexInv, Thm_TypeInv, PTL DEF Spec 

THEOREM Thm_RInv2 == Spec => []RInv2
<1> DEFINE x    == X[I0]
           y    == r[I0]
           m    == lBnd(x) 
           n    == uBnd(x)
           Q(i) == prop(i) /\ red(I0,i)
           f(i) == fr(x,c[I0],i)
<1>1. Init => RInv2
  <2>0. SUFFICES ASSUME Init
                 PROVE  y = M!BigOpP(m,n,Q,f)
    BY DEF RInv2    
  <2>1. /\ I0    \in Seq(Nat)
        /\ I0    \in WDIndex 
        /\ x     \in T       
        /\ It(x) \subseteq Nat
      BY <2>0, H_Type, H_Undef DEF Init, It, WDIndex, wrt
  <2>2. M!BigOpP(m,n,Q,f) = id  
    <3>1. m \in Nat /\ n \in Nat   
      BY <2>1, H_Type DEF m,n       
    <3>2. \A i \in m..n : Q(i) \in BOOLEAN
      BY <2>1, <3>1, m..n \subseteq Nat, H_Type
    <3>3. \A i \in {j \in m..n : Q(j)} : f(i) \in D
      <4>1. \A i \in Nat : ~ red(I0,i)        
        BY <2>0, <2>1 DEF Init
      <4> QED
        BY <2>1, <4>1 DEF It
    <3>4. \A i \in m..n : ~ Q(i)              
      <4>1. \A i \in Nat : ~ red(I0,i)
        BY <2>1, <2>0 DEF Init
      <4> QED     
        BY <2>1, <3>1, <4>1   
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, H_AMon, H_MeqMT, 
         MT!FalsePredicate, Isa 
  <2>3. y = id
    BY <2>0, <2>1 DEF Init       
  <2> QED 
    BY <2>2, <2>3  
<1>2. /\ IndexInv /\ TypeInv /\ TypeInv'
      /\ RInv1 /\ RInv1'
      /\ RInv2
      /\ [Next]_<<in,vs>>
      => RInv2'
  <2>0. SUFFICES ASSUME IndexInv, TypeInv, TypeInv',
                        RInv1, RInv1',
                        RInv2, 
                        [Next]_<<in,vs>>
                 PROVE  RInv2'
    OBVIOUS       
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i)
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE RInv2'
      BY <2>0, <2>A DEF Step, IndexInv    
    <3>1. PICK i \in It(x) : \/ P(I0,i)
                             \/ C(I0,i)
                             \/ R(I0,i)
      BY <3>0 
    <3>2. x \in T
      BY <2>0 DEF IndexInv, TypeInv, WDIndex, wrt   
    <3>3. /\ I0 \in Seq(Nat)
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in {k \in m..n : prop(k)}
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It       
    <3>4. m \in Nat /\ n \in Nat 
      BY <2>0, <3>2, H_Type DEF TypeInv, m, n         
       
    <3>A. CASE P(I0,i)           
      <4>0. SUFFICES ASSUME P(I0,i),
                            y  = M!BigOpP(m,n,Q,f)
                     PROVE  y' = M!BigOpP(m,n,Q,f)
        BY <2>0, <3>A DEF P, RInv2, M!BigOpP, M!BigOp, M!bigOp     
      <4>1. r' = r  BY <4>0 DEF P
      <4>2. y' = y  BY <4>1                  
      <4> QED 
        BY <4>0, <4>2
                
    <3>B. CASE C(I0,i)   
      <4>0. SUFFICES ASSUME C(I0,i),
                            y = M!BigOpP(m,n,Q,f)
                     PROVE  y = M!BigOpP(m,n,Q,f)'
        BY <2>0, <3>B DEF C, RInv2, M!BigOpP, M!BigOp, M!bigOp      
      <4>1. /\ ~ wrt(c[I0][i]) 
            /\ c' = [c EXCEPT ![I0][i] = fc(x,p[I0],i)]
            /\ <<X,r,rs>>' = <<X,r,rs>>  
        BY <4>0 DEF C   
          
      <4> DEFINE fn(j) == fr(x,c[I0]',j)           
      
      <4>2. \A j \in {k \in m..n : Q(k)} : f(j) \in D /\ fn(j) \in D
        <5>0. SUFFICES ASSUME NEW j \in {k \in m..n : Q(k)}
                       PROVE  f(j) \in D /\ fn(j) \in D
          OBVIOUS             
        <5>1. \A k \in It(x) : deps(x,Dep_cr,k) \subseteq It(x)
          BY <3>2, <3>3, H_Type DEF deps, It
        <5>2. /\ It(x)' = It(x)
              /\ m' = m /\ n' = n 
          BY <3>3, <4>1 DEF It         
        <5>A. f(j) \in D
          <6>1. red(I0,j)  
            BY <5>0          
          <6>2. wrts(c[I0],deps(x,Dep_cr,j)) 
            BY <2>0, <6>1 DEF RInv1, It
          <6>3. fr(x,c[I0],j) \in D    
            BY <2>0, <3>2, <3>3, <5>1, <6>2, H_BFunWD DEF It, TypeInv
          <6> QED 
            BY <6>3  
        <5>B. fn(j) \in D
          <6>1. red(I0,j)'  
            BY <4>1, <5>0
          <6>2. wrts(c[I0]',deps(x,Dep_cr,j)) 
            BY <2>0, <5>2, <6>1 DEF RInv1, It, wrts, deps  
          <6>3. fr(x,c[I0]',j) \in D    
            BY <2>0, <3>2, <3>3, <5>1, <5>2, <6>2, H_BFunWD DEF It, TypeInv
          <6> QED 
            BY <6>3            
        <5> QED
          BY <5>A, <5>B       
      
      <4>3. \A j \in {k \in m..n : Q(k)} : f(j) = fn(j)
        <5>0. SUFFICES ASSUME NEW j \in {k \in m..n : Q(k)},
                              j \in It(x)
                       PROVE  f(j) = fn(j)
          BY DEF It          
        <5>1. \A k \in It(x) : k # i => c[I0]'[k] = c[I0][k]
          BY <4>1
        <5>2. red(I0,j) 
          BY <5>0
        <5>3. wrts(c[I0],deps(x,Dep_cr,j))
          BY <2>0, <5>0, <5>2 DEF RInv1
        <5>4. deps(x,Dep_cr,j) \subseteq It(x)
          BY <3>2, <3>3, <5>0, H_Type DEF deps, It 
        <5>5. i \notin deps(x,Dep_cr,j)
          BY <4>1, <5>0, <5>3 DEF wrts  
        <5>6. \A k \in deps(x,Dep_cr,j) :
                wrt(c[I0][k]) /\ c[I0][k] = c[I0]'[k]
          BY <5>0, <5>1, <5>3, <5>4, <5>5 DEF wrts 
        <5>7. c[I0] \in St(Tc) /\ c[I0]' \in St(Tc)
          BY <2>0, <3>3 DEF TypeInv, St 
        <5> QED
          BY <3>2, <3>3, <5>0, <5>6, <5>7, H_frRelevance DEF eqs
      
      <4> HIDE DEF m, n, Q, f, fn
      
      <4>4. M!BigOpP(m,n,Q,f) = M!BigOpP(m,n,Q,fn)
        <5>1. m \in Nat /\ n \in Nat 
          BY <3>4
        <5>2. \A j \in m..n : Q(j) \in BOOLEAN    
          BY DEF Q
        <5>3. /\ \A j \in {k \in m..n : Q(k)} : f(j)  \in D
              /\ \A j \in {k \in m..n : Q(k)} : fn(j) \in D  
          BY <4>2
        <5>4. \A j \in {k \in m..n : Q(k)} : f(j) = fn(j)   
          BY <4>3
        <5>5. MT!BigOpP(m,n,Q,f) = MT!BigOpP(m,n,Q,fn)  
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!FunctionEqP, IsaM("blast") 
        <5> QED    
          BY <5>5, H_MeqMT      
        
      <4>5. M!BigOpP(m,n,Q,f)' = M!BigOpP(m,n,Q,fn)
        <5>1. m' = m /\ n' = n             BY <3>3, <4>1 DEF m, n 
        <5>2. \A j : Q(j) <=> Q(j)         BY <4>1
        <5> QED   
          BY <4>1, <5>1, <5>2 DEF M!BigOpP,M!BigOp,M!bigOp,m,n,Q,f,fn
      
      <4>E1. y' = y                    BY <4>1
      <4>E2.  @ = M!BigOpP(m,n,Q,f)    BY <4>0
      <4>E3.  @ = M!BigOpP(m,n,Q,fn)   BY <4>4
      <4>E4.  @ = M!BigOpP(m,n,Q,f)'   BY <4>5
                         
      <4> QED 
        BY <4>E1, <4>E2, <4>E3, <4>E4                        
                          
    <3>C. CASE R(I0,i) 
      <4>0. SUFFICES ASSUME R(I0,i),
                            y  = M!BigOpP(m,n,Q,f)
                     PROVE  y' = M!BigOpP(m,n,Q,f)'
        BY <2>0, <3>C DEF R, RInv2      
      <4>1. /\ ~ red(I0,i)
            /\ wrts(c[I0],deps(x,Dep_cr,i))
            /\ y'  = Op(y, f(i))
            /\ rs' = [rs EXCEPT ![I0][i] = TRUE]
            /\ <<X,c>>' = <<X,c>>            
        BY <2>0, <4>0, <3>3 DEF TypeInv, R, St             
         
      <4>2. \A j \in {k \in m..n : Q(k)} \union {i} : f(j) \in D 
        <5>0. SUFFICES ASSUME NEW j \in {k \in m..n : Q(k)} \union {i}
                       PROVE  f(j) \in D
          OBVIOUS             
        <5>1. \A k \in It(x) : deps(x,Dep_cr,k) \subseteq It(x)
          BY <3>2, <3>3, H_Type DEF deps, It
        <5>A. CASE j = i
          <6>1. wrts(c[I0],deps(x,Dep_cr,j)) 
            BY <5>A, <4>1
          <6>2. fr(x,c[I0],j) \in D    
            BY <2>0, <3>2, <3>3, <5>1, <5>A, <6>1, H_BFunWD DEF TypeInv
          <6> QED
            BY <6>2 DEF f
        <5>B. CASE j # i
          <6>1. red(I0,j)
            BY <5>0, <5>B
          <6>2. wrts(c[I0],deps(x,Dep_cr,j)) 
            BY <2>0, <6>1 DEF RInv1, It   
          <6>3. fr(x,c[I0],j) \in D    
            BY <2>0, <3>2, <3>3, <5>1, <6>2, H_BFunWD DEF It, TypeInv
          <6> QED  
            BY <6>3 DEF f
        <5> QED
          BY <5>A, <5>B        
         
      <4> DEFINE Q1(j) == Q(j) /\ j # i
                 Q2(j) == prop(j)' /\ red(I0,j)'
                 Q3(j) == Q2(j) /\ j # i   
      <4> HIDE DEF Q, Q1, Q2, Q3, f, m, n 
 
      <4>3. M!BigOpP(m,n,Q,f) = M!BigOpP(m,n,Q1,f)
        <5>1. m \in Nat /\ n \in Nat 
          BY <3>4    
        <5>2. \A j \in {k \in m..n : Q(k) /\ Q1(k)} : f(j) \in D 
          BY <4>2 DEF It, m, n, Q, Q1         
        <5>3. /\ \A j \in m..n : Q(j)  \in BOOLEAN  
              /\ \A j \in m..n : Q1(j) \in BOOLEAN  
          BY DEF Q, Q1
        <5>4. \A j \in m..n : Q(j) <=> Q1(j)       
          BY <4>1, ~ red(I0,i) DEF Q, Q1
        <5>5. MT!BigOpP(m,n,Q,f) = MT!BigOpP(m,n,Q1,f)
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!PredicateEq, Isa        
        <5> QED 
          BY <5>5, H_MeqMT
  
      <4>4. M!BigOpP(m,n,Q1,f) = M!BigOpP(m,n,Q3,f)
        <5>1. m \in Nat /\ n \in Nat 
          BY <3>4     
        <5>2. \A j \in {k \in m..n : Q1(k) /\ Q3(k)} : f(j) \in D
          BY <4>2 DEF It, m, n, Q1, Q3, Q2, Q           
        <5>3. /\ \A j \in m..n : Q1(j) \in BOOLEAN
              /\ \A j \in m..n : Q3(j) \in BOOLEAN  
          BY DEF Q1, Q3
        <5>4. \A j \in m..n : Q1(j) <=> Q3(j)       
          <6>1. It(I0)' = It(I0)           
            BY <4>1 DEF It, m, n
          <6>2. y' # Undef 
            BY <2>0, <4>1, H_Undef DEF TypeInv
          <6>3. red(I0,i)'
            BY <2>0, <3>3, <4>1, <6>1, <6>2 DEF TypeInv, St
          <6> QED
            BY <4>1, <6>3 DEF Q1, Q3, Q, Q2
        <5>5. MT!BigOpP(m,n,Q1,f) = MT!BigOpP(m,n,Q3,f)
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!PredicateEq, Isa        
        <5> QED 
          BY <5>5, H_MeqMT
       
      <4>5. M!BigOpP(m,n,Q2,f) = Op(M!BigOpP(m,n,Q3,f), f(i))  
        <5>1. m \in Nat /\ n \in Nat /\ m <= n    
          BY <3>3, <3>4 
        <5>2. i \in m..n /\ Q2(i) 
          <6>1. It(I0)' = It(I0)           
            BY <4>1 DEF It, m, n
          <6>2. y' # Undef 
            BY <2>0, <4>1, H_Undef DEF TypeInv
          <6>3. red(I0,i)'
            BY <2>0, <3>3, <4>1, <6>1, <6>2 DEF TypeInv, St
          <6> QED  
            BY <3>3, <6>3 DEF Q2
        <5>3. \A j \in m..n : Q2(j) \in BOOLEAN 
          BY <3>3, H_Type DEF Q2
        <5>4. \A j \in {k \in m..n : Q2(k)} : f(j) \in D
          <6>1. {k \in m..n : Q2(k)} = {k \in m..n : Q(k)} \union {i}
            <7>1. red(I0,i)'
              BY <2>0, <3>3, <4>1 DEF TypeInv                            
            <7>2. \A j \in It(x) \ {i} : red(I0,j)' = red(I0,j)
              BY <4>1
            <7> QED 
              BY <3>3, <7>1, <7>2 DEF Q, Q2, m, n, It
          <6> QED
            BY <4>2, <6>1 DEF It, m, n, Q, Q2
        <5>5. MT!BigOpP(m,n,Q2,f) = Op(MT!BigOpP(m,n,Q3,f), f(i))
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!SplitRandomP, Isa DEF Q3
        <5> QED
          BY <5>5, H_MeqMT   
              
      <4>6. M!BigOpP(m,n,Q,f)' = M!BigOpP(m,n,Q2,f)
        <5>1. m' = m /\ n' = n             BY <4>1 DEF m, n 
        <5>2. \A j : f(j)' = f(j)          BY <4>1 DEF f
        <5> QED   
          BY <5>1, <5>2 DEF Q, Q2, M!BigOpP, M!BigOp, M!bigOp, Isa 
        
      <4>E1. y' = Op(y, f(i))                      BY <4>1
      <4>E2.  @ = Op(M!BigOpP(m,n,Q,f),  f(i))     BY <4>0
      <4>E3.  @ = Op(M!BigOpP(m,n,Q1,f), f(i))     BY <4>3
      <4>E4.  @ = Op(M!BigOpP(m,n,Q3,f), f(i))     BY <4>4
      <4>E5.  @ = M!BigOpP(m,n,Q2,f)               BY <4>5
      <4>E6.  @ = M!BigOpP(m,n,Q,f)'               BY <4>6
        
      <4> QED      
        BY <4>E1, <4>E2, <4>E3, <4>E4, <4>E5, <4>E6   
                    
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C               
  <2>B. CASE Done  
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          y  = M!BigOpP(m,n,Q,f)
                   PROVE  y' = M!BigOpP(m,n,Q,f)
      BY <2>0, <2>B DEF Done, vs, RInv2, M!BigOpP, M!BigOp, M!bigOp
    <3>1. y' = y    
      BY <3>0 DEF vs
    <3> QED
      BY <3>0, <3>1    
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          y  = M!BigOpP(m,n,Q,f)
                   PROVE  y' = M!BigOpP(m,n,Q,f)
      BY <2>0, <2>C DEF vs, RInv2, M!BigOpP, M!BigOp, M!bigOp
    <3>1. y' = y    
      BY <3>0 DEF vs
    <3> QED
      BY <3>0, <3>1     
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next          
<1> QED 
  BY <1>1, <1>2, Thm_IndexInv, Thm_TypeInv, Thm_RInv1, PTL DEF Spec

THEOREM Thm_Inv == Spec => []Inv
  BY Thm_IndexInv, Thm_TypeInv, Thm_PInv, Thm_CInv, 
     Thm_RInv1, Thm_RInv2, PTL DEF Inv

THEOREM Thm_Correctness == Spec => []Correctness
<1> DEFINE x    == X[I0]
           y    == r[I0]
           m    == lBnd(x) 
           n    == uBnd(x)
           Q(j) == prop(j)
           f(i) == Fr(x,Fc(x,Gp(x)))[i]
<1>1. Init => Correctness
  <2>0. SUFFICES ASSUME Init,
                        end(I0)
                 PROVE  y = A(x)
    BY DEF Correctness
  <2>1. /\ I0    \in Seq(Nat) 
        /\ x     \in T        
        /\ It(x) \subseteq Nat
      BY <2>0, H_Type DEF Init, It
  <2>A. CASE It(x) = {}
    <3>1. m \in Nat /\ n \in Nat   BY <2>1, H_Type          
    <3>A. CASE m > n 
      <4>1. A(x) = id 
        BY <3>1, <3>A, H_AMon, H_MeqMT, 
           MT!EmptyIntvAssumpP DEF A
      <4>2. y = id
        BY <2>0, <2>1 DEF Init  
      <4> QED
        BY <4>1, <4>2
    <3>B. CASE \A i \in m..n : ~ Q(i)     
      <4>1. \A i \in m..n : Q(i) \in BOOLEAN
        BY <3>1, m..n \subseteq Nat, H_Type
      <4>2. \A i \in {j \in m..n : Q(j)} : f(i) \in D
        BY <2>A, <2>1, <3>1 DEF f, It   
      <4> HIDE DEF m, n, Q, f     
      <4>3. M!BigOpP(m,n,Q,f) = id 
        BY <3>1, <3>B, <4>1, <4>2, H_AMon, H_MeqMT, 
           MT!FalsePredicate, Isa DEF A     
      <4>4. A(x) = id
        BY <4>3 DEF A, f   
      <4>5. y = id
        BY <2>0, <2>1 DEF Init  
      <4> QED
        BY <4>4, <4>5           
    <3> QED
      BY <2>A, <3>A, <3>B DEF It
  <2>B. CASE It(x) # {}
    <3>1. \A i \in It(x) : red(I0,i)       BY <2>0 DEF end   
    <3>2. \A i \in Nat : ~ red(I0,i)       BY <2>0, <2>1 DEF Init
    <3>3. FALSE                            BY <2>1, <2>B, <3>1, <3>2   
    <3> QED                                BY <3>3
  <2> QED 
    BY <2>A, <2>B
<1>2. /\ Inv 
      /\ Correctness
      /\ [Next]_<<in,vs>>
      => Correctness'
  <2>0. SUFFICES ASSUME IndexInv, TypeInv, PInv,
                        CInv, RInv1, RInv2,
                        Correctness,
                        [Next]_<<in,vs>>
                 PROVE  Correctness'
    BY DEF Inv 
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i)
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE Correctness'
      BY <2>0, <2>A DEF Step, IndexInv    
    <3>1. PICK i \in It(x) : \/ P(I0,i) 
                             \/ C(I0,i)
                             \/ R(I0,i)
      BY <3>0 
    <3>2. x \in T
      BY <2>0 DEF IndexInv, TypeInv, WDIndex, wrt
    <3>3. /\ I0 \in Seq(Nat) 
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in {k \in m..n : Q(k)} 
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It       
    <3>4. m \in Nat /\ n \in Nat 
      BY <2>0, <3>2, H_Type DEF TypeInv, m, n     
    <3>5. \A j \in It(x) : 
            /\ red(I0,j)     => wrt(c[I0][j])
            /\ wrt(c[I0][j]) => wrt(p[I0][j])
      BY <2>0 DEF CInv, RInv1, wrts, deps

    <3>A. CASE P(I0,i)    
      <4>0. SUFFICES ASSUME P(I0,i),
                            end(I0)'
                     PROVE  FALSE
         BY <2>0, <3>A DEF P, Correctness 
      <4>1. /\ ~ wrt(p[I0][i])
            /\ <<X,rs>>' = <<X,rs>>           BY <4>0 DEF P                        
      <4>2. ~ wrt(p[I0][i]) => ~ red(I0,i)    BY <3>5
      <4>3. ~ red(I0,i)                       BY <4>1, <4>2
      <4>4. ~ red(I0,i)'                      BY <4>1, <4>3
      <4>5. \E j \in It(x)' : ~ red(I0,j)'    BY <4>1, <4>4 DEF It
      <4>6. FALSE                             BY <4>5, end(I0)' DEF end                   
      <4> QED 
        BY <4>6
        
    <3>B. CASE C(I0,i)
      <4>0. SUFFICES ASSUME C(I0,i),
                            end(I0)'
                     PROVE  FALSE
         BY <2>0, <3>B DEF C, Correctness     
      <4>1. /\ ~ wrt(c[I0][i])
            /\ <<X,rs>>' = <<X,rs>>          BY <4>0 DEF C     
      <4>2. ~ wrt(c[I0][i]) => ~ red(I0,i)   BY <3>5
      <4>3. ~ red(I0,i)                      BY <4>1, <4>2
      <4>4. ~ red(I0,i)'                     BY <4>1, <4>3
      <4>5. \E j \in It(x)' : ~ red(I0,j)'   BY <4>1, <4>4 DEF It
      <4>6. FALSE                            BY <4>5, end(I0)' DEF end                   
      <4> QED 
        BY <4>6  
          
    <3>C. CASE R(I0,i)     
      <4>0. SUFFICES ASSUME R(I0,i),
                            end(I0)'
                     PROVE  y' = A(x)
        BY <2>0, <3>C DEF R, Correctness, A, M!BigOpP, M!BigOp, M!bigOp      
      <4> DEFINE g(j) == fr(x,c[I0],j)                         
      <4>1. /\ ~ red(I0,i)
            /\ wrts(c[I0],deps(x,Dep_cr,i))
            /\ y'  = Op(y, g(i))
            /\ rs' = [rs EXCEPT ![I0][i] = TRUE]
            /\ X'  = X            
        BY <2>0, <4>0, <3>3 DEF TypeInv, R, St 
              
      <4>2. /\ \A j \in It(x)\{i} : red(I0,j)
            /\ ~ red(I0,i) 
        <5>1. It(x)' = It(x)           
          BY <4>1 DEF It, m, n    
        <5>2. ~ red(I0,i)
          BY <4>1
        <5>3. rs' = [rs EXCEPT ![I0][i] = TRUE]
          BY <4>1                 
        <5>4. \A j \in It(x) : red(I0,j)'
          BY <4>0, <5>1 DEF end
        <5> QED 
          BY <5>2, <5>3, <5>4         
           
      <4>3. /\ \A j \in It(x) : wrt(c[I0][j]) 
            /\ \A j \in It(x) : wrt(p[I0][j])        
        <5>1. \A j \in It(x) : wrt(c[I0][j])                
          <6>1. wrt(c[I0][i]) 
            BY <4>1 DEF wrts, deps
          <6>2. \A j \in It(x)\{i} : wrt(c[I0][j])
            BY <2>0, <3>3, <3>5, <4>2
          <6> QED
            BY <2>0, <3>3, <6>1, <6>2
        <5>2. \A j \in It(x) : wrt(p[I0][j])
          BY <3>5, <5>1 
        <5> QED
          BY <5>1, <5>2   
            
      <4>4. /\ \A j \in It(x) : Gp(x)[j] = p[I0][j]
            /\ Gp(x) \in St(Tp) /\ p[I0] \in St(Tp)        
        <5>1. Gp(x) \in St(Tp)
          <6>1. \A j \in Nat : gp(x,j) \in Tp \union {Undef}
            BY <3>2, <3>3, H_BFunType
          <6> QED 
            BY <3>3, <6>1 DEF Gp, St                 
        <5>2. p[I0] \in St(Tp)
          BY <2>0, <3>3 DEF TypeInv                                              
        <5>3. \A j \in It(x) : Gp(x)[j] = p[I0][j]
          <6>0. SUFFICES ASSUME NEW j \in It(x) 
                         PROVE  gp(x,j) = fp(x,p[I0],j)
            BY <2>0, <3>3, <4>3 DEF PInv, Gp           
          <6> QED 
            BY <3>2, <4>3, H_ProdEqInv                      
        <5> QED 
          BY <5>1, <5>2, <5>3 DEF St     
      
      <4>5. /\ \A j \in It(x) : Fc(x,Gp(x))[j] = c[I0][j]
            /\ Fc(x,Gp(x)) \in St(Tc) /\ c[I0] \in St(Tc)               
        <5>1. Fc(x,Gp(x)) \in St(Tc)   
          <6>1. \A j \in Nat : fc(x,Gp(x),j) \in Tc \union {Undef}
            BY <3>2, <3>3, <4>4, H_BFunType
          <6> QED 
            BY <3>3, <6>1 DEF Fc, St 
        <5>2. c[I0] \in St(Tc)
          BY <2>0, <3>3 DEF TypeInv                                       
        <5>3. \A j \in It(x) : Fc(x,Gp(x))[j] = c[I0][j]
          <6>0. SUFFICES ASSUME NEW j \in It(x) 
                         PROVE  fc(x,Gp(x),j) = fc(x,p[I0],j)
            BY <2>0, <3>3, <4>3 DEF CInv, Fc        
          <6>1. eqs(Gp(x),p[I0],deps(x,Dep_pc,j))
            <7>1. deps(x,Dep_pc,j) \subseteq It(x)  
              BY <3>2, <3>3, H_Type DEF deps, It
            <7>2. wrts(p[I0],deps(x,Dep_pc,j))
              BY <4>3, <7>1 DEF wrts
            <7>3. \A k \in deps(x,Dep_pc,j) :
                    wrt(p[I0][k]) /\ Gp(x)[k] = p[I0][k]
              BY <4>4, <7>1, <7>2 DEF wrts         
            <7> QED  
              BY <7>3 DEF eqs                
          <6>2. Gp(x) \in St(Tp) /\ p[I0] \in St(Tp)
            BY <4>4                                             
          <6>3. fc(x,Gp(x),j) = fc(x,p[I0],j)
            BY <3>2, <3>3, <6>1, <6>2, H_fcRelevance     
          <6> QED 
            BY <6>3                                     
        <5> QED  
          BY <5>1, <5>2, <5>3 DEF St  
      
      <4>6. /\ \A j \in It(x) : f(j) = g(j)
            /\ \A j \in It(x) : f(j) \in D /\ g(j) \in D      
        <5>1. \A j \in It(x) : f(j) = g(j)
          <6>0. SUFFICES ASSUME NEW j \in It(x)
                         PROVE  fr(x,Fc(x,Gp(x)),j) = fr(x,c[I0],j)
            BY <3>3 DEF Fr
          <6>1. eqs(Fc(x,Gp(x)),c[I0],deps(x,Dep_cr,j))              
            <7>1. deps(x,Dep_cr,j) \subseteq It(x)  
              BY <3>2, <3>3, H_Type DEF deps, It
            <7>2. wrts(c[I0],deps(x,Dep_cr,j))
              BY <4>3, <7>1 DEF wrts              
            <7>3. \A k \in deps(x,Dep_cr,j) :
                    wrt(c[I0][k]) /\ Fc(x,Gp(x))[k] = c[I0][k]
              BY <4>5, <7>1, <7>2 DEF wrts         
            <7> QED  
              BY <7>3 DEF eqs  
          <6>2. Fc(x,Gp(x)) \in St(Tc) /\ c[I0] \in St(Tc)
            BY <4>5                              
          <6>3. fr(x,Fc(x,Gp(x)),j) = fr(x,c[I0],j)
            BY <3>2, <3>3, <6>1, <6>2, H_frRelevance     
          <6> QED 
            BY <6>3                     
        <5>2. \A j \in It(x) : f(j) \in D     
          <6>1. \A j \in It(x) : deps(x,Dep_cr,j) \subseteq It(x)
            BY <3>2, <3>3, H_Type DEF deps,It 
          <6>2. \A j \in It(x) : fr(x,Fc(x,Gp(x)),j) \in D  
            BY <3>2, <4>3, <4>5, <6>1, H_BFunWD DEF wrts
          <6> QED
            BY <3>3, <6>2 DEF Fr, St 
        <5>3. \A j \in It(x) : g(j) \in D                   
          <6>1. \A j \in It(x) : deps(x,Dep_cr,j) \subseteq It(x)
            BY <3>2, <3>3, H_Type DEF deps, It
          <6>2. \A j \in It(x) : fr(x,c[I0],j) \in D
            BY <3>2, <4>3, <4>5, <6>1, H_BFunWD DEF wrts                        
          <6> QED     
            BY <6>2          
        <5> QED
          BY <5>1, <5>2, <5>3
          
      <4> DEFINE Q1(j) == Q(j) /\ j # i
                 Q2(j) == Q(j) /\ red(I0,j)
      <4> HIDE DEF Q, Q1, Q2, f, g, m, n 
            
      <4>7. M!BigOpP(m,n,Q,f) = Op(M!BigOpP(m,n,Q1,f), f(i))
        <5>1. m \in Nat /\ n \in Nat /\ m <= n
          BY <3>3, <3>4 
        <5>2. i \in m..n /\ Q(i)  
          BY <3>3 DEF Q
        <5>3. \A j \in m..n : Q(j) \in BOOLEAN
          BY <3>3, <3>2, H_Type, m..n \subseteq Nat DEF It, Q, m, n
        <5>4. \A j \in {k \in m..n : Q(k)} : f(j) \in D
          BY <4>6 DEF It, m, n, Q
        <5>5. MT!BigOpP(m,n,Q,f) = Op(MT!BigOpP(m,n,Q1,f), f(i))
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!SplitRandomP, Isa DEF Q1
        <5> QED
          BY <5>5, H_MeqMT
      
      <4>8. M!BigOpP(m,n,Q1,f) = M!BigOpP(m,n,Q2,f)
        <5>1. m \in Nat /\ n \in Nat 
          BY <3>4   
        <5>2. \A j \in {k \in m..n : Q1(k) /\ Q2(k)} : f(j) \in D 
          BY <4>6 DEF Q, Q1, Q2, It, m, n       
        <5>3. /\ \A j \in m..n : Q1(j) \in BOOLEAN  
              /\ \A j \in m..n : Q2(j) \in BOOLEAN  
          BY DEF Q1, Q2
        <5>4. \A j \in m..n : Q1(j) <=> Q2(j)       
          BY <3>3, <3>4, <4>2 DEF It, Q, Q1, Q2, m, n 
        <5>5. MT!BigOpP(m,n,Q1,f) = MT!BigOpP(m,n,Q2,f)    
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!PredicateEq, Isa
        <5> QED 
          BY <5>5, H_MeqMT
                       
      <4>9. /\ M!BigOpP(m,n,Q2,f) = M!BigOpP(m,n,Q2,g)
            /\ f(i) = g(i)
        <5>1. m \in Nat /\ n \in Nat 
          BY <3>4
        <5>2. \A j \in m..n : Q2(j) \in BOOLEAN    
          BY DEF Q2
        <5>3. /\ \A j \in {k \in m..n : Q2(k)} : f(j) \in D
              /\ \A j \in {k \in m..n : Q2(k)} : g(j) \in D  
          BY <4>6 DEF Q, Q2, It, m, n
        <5>4. \A j \in {k \in m..n : Q2(k)} : f(j) = g(j)   
          BY <2>0, <3>3, <4>6 DEF Q, Q2, It, m, n 
        <5>5. MT!BigOpP(m,n,Q2,f) = MT!BigOpP(m,n,Q2,g)  
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!FunctionEqP, IsaM("blast") 
        <5>6. f(i) = g(i) 
          BY <4>6 
        <5> QED    
          BY <5>5, <5>6, H_MeqMT

      <4>E1. A(x) = M!BigOpP(m,n,Q,f)              BY DEF A, Q, f, m, n 
      <4>E2.    @ = Op(M!BigOpP(m,n,Q1,f), f(i))   BY <4>7
      <4>E3.    @ = Op(M!BigOpP(m,n,Q2,f), f(i))   BY <4>8
      <4>E4.    @ = Op(M!BigOpP(m,n,Q2,g), g(i))   BY <4>9
      <4>E5.    @ = Op(y, g(i))                    BY <2>0, <3>3 DEF RInv2,Q,Q2,g,m,n
      <4>E6.    @ = y'                             BY <4>1      
      
      <4> QED
        BY <4>E1, <4>E2, <4>E3, <4>E4, <4>E5, <4>E6       
              
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C         
  <2>B. CASE Done  
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          end(I0)
                   PROVE  y' = A(x)
      BY <2>B DEF Done, vs, A, M!BigOpP, M!BigOp, M!bigOp, end
    <3>1. y = A(x)     
      BY <2>0, <3>0 DEF Correctness
    <3>2. y' = y
      BY <3>0 DEF vs 
    <3> QED
      BY <3>1, <3>2    
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          end(I0)
                   PROVE  y' = A(x)
      BY <2>C DEF vs, Correctness, A, M!BigOpP, M!BigOp, M!bigOp, end
    <3>1. y = A(x)     
      BY <2>0, <3>0 DEF Correctness
    <3>2. y' = y
      BY <3>0 DEF vs 
    <3> QED
      BY <3>1, <3>2    
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next
<1> QED 
  BY <1>1, <1>2, Thm_Inv, PTL DEF Spec 

LEMMA H_A1stepEqA == ASSUME NEW x
                     PROVE  A1step!A(x) = A(x)
  BY DEF A1step!A, A,
         A1step!M!BigOpP, A1step!M!BigOp, A1step!M!bigOp, M!BigOpP, M!BigOp, M!bigOp,
         A1step!Assig, A1step!Fr, A1step!Fc, A1step!Gp, Assig, Fr, Fc, Gp

THEOREM Thm_Refinement == Spec => A1step!Spec
<1> DEFINE x    == X[I0]
           y    == r[I0]
           m    == lBnd(x) 
           n    == uBnd(x)
           Q(j) == prop(j)
           f(i) == Fr(x,Fc(x,Gp(x)))[i]
<1>1. Init => A1step!Init
  <2> SUFFICES ASSUME Init
               PROVE  A1step!Init
    OBVIOUS
  <2>1. /\ x \in T
        /\ pre(x)
        /\ y = id
    BY H_Type DEF Init    
  <2> QED 
    BY <2>1 DEF A1step!Init, inS, outS 
<1>2. /\ Inv 
      /\ Correctness'
      /\ [Next]_<<in,vs>>
      => [A1step!Next]_A1step!vs
  <2>0. SUFFICES ASSUME IndexInv, TypeInv, PInv,
                        CInv, RInv1, RInv2,
                        Correctness',
                        [Next]_<<in,vs>>
                 PROVE  [A1step!Next]_<<inS,outS>>
    BY DEF A1step!vs, Inv
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i)
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE [A1step!Next]_<<inS,outS>>
      BY <2>0, <2>A DEF Step, IndexInv    
    <3>1. PICK i \in It(x) : \/ P(I0,i)
                             \/ C(I0,i)
                             \/ R(I0,i)
      BY <3>0 
    <3>2. x \in T
      BY <2>0 DEF IndexInv, TypeInv, WDIndex, wrt
    <3>3. /\ I0 \in Seq(Nat) 
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in {k \in m..n : Q(k)} 
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It       
    <3>4. m \in Nat /\ n \in Nat 
      BY <2>0, <3>2, H_Type DEF TypeInv, m, n     
    <3>5. \A j \in It(x) : 
            /\ red(I0,j)     => wrt(c[I0][j])
            /\ wrt(c[I0][j]) => wrt(p[I0][j])
      BY <2>0 DEF CInv, RInv1, wrts, deps

    <3>A. CASE P(I0,i)    
      <4>0. SUFFICES ASSUME P(I0,i)
                     PROVE  UNCHANGED <<inS,outS>>
         BY <2>0, <3>A DEF P
      <4>1. /\ ~ wrt(p[I0][i])
            /\ <<X,rs>>' = <<X,rs>>           BY <4>0 DEF P                
      <4>2. ~ wrt(p[I0][i]) => ~ red(I0,i)    BY <3>5
      <4>3. ~ red(I0,i)                       BY <4>1, <4>2
      <4>4. ~ end(I0)                         BY <4>3 DEF end
      <4>5. ~ end(I0)'                        BY <4>4, <4>1 DEF end, It
      <4>6. <<inS,outS>>' = <<inS,outS>>      BY <4>1, <4>4, <4>5 DEF inS, outS                  
      <4> QED 
        BY <4>6
    
    <3>B. CASE C(I0,i)
      <4>0. SUFFICES ASSUME C(I0,i)
                     PROVE  UNCHANGED <<inS,outS>>
        BY <2>0, <3>B DEF C
      <4>1. /\ ~ wrt(c[I0][i])
            /\ <<X,rs>>' = <<X,rs>>           BY <4>0 DEF C                
      <4>2. ~ wrt(c[I0][i]) => ~ red(I0,i)    BY <3>5
      <4>3. ~ red(I0,i)                       BY <4>1, <4>2
      <4>4. ~ end(I0)                         BY <4>3 DEF end
      <4>5. ~ end(I0)'                        BY <4>4, <4>1 DEF end, It
      <4>6. <<inS,outS>>' = <<inS,outS>>      BY <4>1, <4>4, <4>5 DEF inS, outS                  
      <4> QED 
        BY <4>6    
    
    <3>C. CASE R(I0,i) /\ end(I0)'
      <4>0. SUFFICES ASSUME R(I0,i),
                            end(I0)'
                     PROVE  outS' = A1step!A(x)
        BY <2>0, <3>C DEF R, A1step!Next, inS    
      <4> DEFINE g(j) == fr(x,c[I0],j)                         
      <4>1. /\ ~ red(I0,i)
            /\ wrts(c[I0],deps(x,Dep_cr,i))
            /\ y'  = Op(y, g(i))
            /\ rs' = [rs EXCEPT ![I0][i] = TRUE]
            /\ X'  = X
        BY <2>0, <4>0, <3>3 DEF TypeInv, R, St
        
      <4>2. /\ \A j \in It(x)\{i} : red(I0,j)
            /\ ~ red(I0,i) 
        <5>1. It(x)' = It(x)           
          BY <4>1 DEF It, m, n    
        <5>2. ~ red(I0,i)
          BY <4>1
        <5>3. rs' = [rs EXCEPT ![I0][i] = TRUE]
          BY <4>1                 
        <5>4. \A j \in It(x) : red(I0,j)'
          BY <4>0, <5>1 DEF end
        <5> QED 
          BY <5>2, <5>3, <5>4 
           
      <4>3. /\ \A j \in It(x) : wrt(c[I0][j]) 
            /\ \A j \in It(x) : wrt(p[I0][j])        
        <5>1. \A j \in It(x) : wrt(c[I0][j])                
          <6>1. wrt(c[I0][i]) 
            BY <4>1 DEF wrts, deps
          <6>2. \A j \in It(x)\{i} : wrt(c[I0][j])
            BY <2>0, <3>3, <3>5, <4>2
          <6> QED
            BY <2>0, <3>3, <6>1, <6>2
        <5>2. \A j \in It(x) : wrt(p[I0][j])
          BY <3>5, <5>1 
        <5> QED
          BY <5>1, <5>2   
      
      <4>4. /\ \A j \in It(x) : Gp(x)[j] = p[I0][j]
            /\ Gp(x) \in St(Tp) /\ p[I0] \in St(Tp)        
        <5>1. Gp(x) \in St(Tp)
          <6>1. \A j \in Nat : gp(x,j) \in Tp \union {Undef}
            BY <3>2, <3>3, H_BFunType
          <6> QED 
            BY <3>3, <6>1 DEF Gp, St                 
        <5>2. p[I0] \in St(Tp)
          BY <2>0, <3>3 DEF TypeInv                                              
        <5>3. \A j \in It(x) : Gp(x)[j] = p[I0][j]
          <6>0. SUFFICES ASSUME NEW j \in It(x) 
                         PROVE  gp(x,j) = fp(x,p[I0],j)
            BY <2>0, <3>3, <4>3 DEF PInv, Gp           
          <6> QED 
            BY <3>2, <4>3, H_ProdEqInv                      
        <5> QED 
          BY <5>1, <5>2, <5>3 DEF St     
      
      <4>5. /\ \A j \in It(x) : Fc(x,Gp(x))[j] = c[I0][j]
            /\ Fc(x,Gp(x)) \in St(Tc) /\ c[I0] \in St(Tc)               
        <5>1. Fc(x,Gp(x)) \in St(Tc)   
          <6>1. \A j \in Nat : fc(x,Gp(x),j) \in Tc \union {Undef}
            BY <3>2, <3>3, <4>4, H_BFunType
          <6> QED 
            BY <3>3, <6>1 DEF Fc, St 
        <5>2. c[I0] \in St(Tc)
          BY <2>0, <3>3 DEF TypeInv                                       
        <5>3. \A j \in It(x) : Fc(x,Gp(x))[j] = c[I0][j]
          <6>0. SUFFICES ASSUME NEW j \in It(x) 
                         PROVE  fc(x,Gp(x),j) = fc(x,p[I0],j)
            BY <2>0, <3>3, <4>3 DEF CInv, Fc        
          <6>1. eqs(Gp(x),p[I0],deps(x,Dep_pc,j))
            <7>1. deps(x,Dep_pc,j) \subseteq It(x)  
              BY <3>2, <3>3, H_Type DEF deps, It
            <7>2. wrts(p[I0],deps(x,Dep_pc,j))
              BY <4>3, <7>1 DEF wrts
            <7>3. \A k \in deps(x,Dep_pc,j) : 
                    wrt(p[I0][k]) /\ Gp(x)[k] = p[I0][k]
              BY <4>4, <7>1, <7>2 DEF wrts         
            <7> QED  
              BY <7>3 DEF eqs                
          <6>2. Gp(x) \in St(Tp) /\ p[I0] \in St(Tp)
            BY <4>4                                             
          <6>3. fc(x,Gp(x),j) = fc(x,p[I0],j)
            BY <3>2, <3>3, <6>1, <6>2, H_fcRelevance     
          <6> QED 
            BY <6>3                                     
        <5> QED  
          BY <5>1, <5>2, <5>3 DEF St  
      
      <4>6. /\ \A j \in It(x) : f(j) = g(j)
            /\ \A j \in It(x) : f(j) \in D /\ g(j) \in D      
        <5>1. \A j \in It(x) : f(j) = g(j)
          <6>0. SUFFICES ASSUME NEW j \in It(x)
                         PROVE  fr(x,Fc(x,Gp(x)),j) = fr(x,c[I0],j)
            BY <3>3 DEF Fr
          <6>1. eqs(Fc(x,Gp(x)),c[I0],deps(x,Dep_cr,j))              
            <7>1. deps(x,Dep_cr,j) \subseteq It(x)  
              BY <3>2, <3>3, H_Type DEF deps, It
            <7>2. wrts(c[I0],deps(x,Dep_cr,j))
              BY <4>3, <7>1 DEF wrts              
            <7>3. \A k \in deps(x,Dep_cr,j) :
                    wrt(c[I0][k]) /\ Fc(x,Gp(x))[k] = c[I0][k]
              BY <4>5, <7>1, <7>2 DEF wrts         
            <7> QED  
              BY <7>3 DEF eqs  
          <6>2. Fc(x,Gp(x)) \in St(Tc) /\ c[I0] \in St(Tc)
            BY <4>5                              
          <6>3. fr(x,Fc(x,Gp(x)),j) = fr(x,c[I0],j)
            BY <3>2, <3>3, <6>1, <6>2, H_frRelevance     
          <6> QED 
            BY <6>3                     
        <5>2. \A j \in It(x) : f(j) \in D     
          <6>1. \A j \in It(x) : deps(x,Dep_cr,j) \subseteq It(x)
            BY <3>2, <3>3, H_Type DEF deps,It 
          <6>2. \A j \in It(x) : fr(x,Fc(x,Gp(x)),j) \in D  
            BY <3>2, <4>3, <4>5, <6>1, H_BFunWD DEF wrts
          <6> QED
            BY <3>3, <6>2 DEF Fr, St 
        <5>3. \A j \in It(x) : g(j) \in D                   
          <6>1. \A j \in It(x) : deps(x,Dep_cr,j) \subseteq It(x)
            BY <3>2, <3>3, H_Type DEF deps, It
          <6>2. \A j \in It(x) : fr(x,c[I0],j) \in D
            BY <3>2, <4>3, <4>5, <6>1, H_BFunWD DEF wrts                        
          <6> QED     
            BY <6>2          
        <5> QED
          BY <5>1, <5>2, <5>3
          
      <4> DEFINE Q1(j) == Q(j) /\ j # i
                 Q2(j) == Q(j) /\ red(I0,j)
      <4> HIDE DEF Q, Q1, Q2, f, g, m, n 
            
      <4>7. M!BigOpP(m,n,Q,f) = Op(M!BigOpP(m,n,Q1,f), f(i))
        <5>1. m \in Nat /\ n \in Nat /\ m <= n
          BY <3>3, <3>4 
        <5>2. i \in m..n /\ Q(i)  
          BY <3>3 DEF Q
        <5>3. \A j \in m..n : Q(j) \in BOOLEAN
          BY <3>3, <3>2, H_Type, m..n \subseteq Nat DEF It, Q, m, n
        <5>4. \A j \in {k \in m..n : Q(k)} : f(j) \in D
          BY <4>6 DEF It, m, n, Q
        <5>5. MT!BigOpP(m,n,Q,f) = Op(MT!BigOpP(m,n,Q1,f), f(i))
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!SplitRandomP, Isa DEF Q1
        <5> QED
          BY <5>5, H_MeqMT
      
      <4>8. M!BigOpP(m,n,Q1,f) = M!BigOpP(m,n,Q2,f)
        <5>1. m \in Nat /\ n \in Nat 
          BY <3>4   
        <5>2. \A j \in {k \in m..n : Q1(k) /\ Q2(k)} : f(j) \in D 
          BY <4>6 DEF Q, Q1, Q2, It, m, n       
        <5>3. /\ \A j \in m..n : Q1(j) \in BOOLEAN
              /\ \A j \in m..n : Q2(j) \in BOOLEAN  
          BY DEF Q1, Q2
        <5>4. \A j \in m..n : Q1(j) <=> Q2(j)       
          BY <3>3, <3>4, <4>2 DEF It, Q, Q1, Q2, m, n 
        <5>5. MT!BigOpP(m,n,Q1,f) = MT!BigOpP(m,n,Q2,f)    
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!PredicateEq, Isa
        <5> QED 
          BY <5>5, H_MeqMT
                       
      <4>9. /\ M!BigOpP(m,n,Q2,f) = M!BigOpP(m,n,Q2,g)
            /\ f(i) = g(i) 
        <5>1. m \in Nat /\ n \in Nat 
          BY <3>4
        <5>2. \A j \in m..n : Q2(j) \in BOOLEAN    
          BY DEF Q2
        <5>3. /\ \A j \in {k \in m..n : Q2(k)} : f(j) \in D
              /\ \A j \in {k \in m..n : Q2(k)} : g(j) \in D  
          BY <4>6 DEF Q, Q2, It, m, n
        <5>4. \A j \in {k \in m..n : Q2(k)} : f(j) = g(j)   
          BY <2>0, <3>3, <4>6 DEF Q, Q2, It, m, n 
        <5>5. MT!BigOpP(m,n,Q2,f) = MT!BigOpP(m,n,Q2,g)  
          BY <5>1, <5>2, <5>3, <5>4, H_AMon, MT!FunctionEqP, IsaM("blast") 
        <5>6. f(i) = g(i) 
          BY <4>6 
        <5> QED    
          BY <5>5, <5>6, H_MeqMT

      <4>E1. A(x) = M!BigOpP(m,n,Q,f)              BY DEF A, Q, f, m, n 
      <4>E2.    @ = Op(M!BigOpP(m,n,Q1,f), f(i))   BY <4>7
      <4>E3.    @ = Op(M!BigOpP(m,n,Q2,f), f(i))   BY <4>8
      <4>E4.    @ = Op(M!BigOpP(m,n,Q2,g), g(i))   BY <4>9
      <4>E5.    @ = Op(y, g(i))                    BY <2>0, <3>3 DEF RInv2,Q,Q2,g,m,n
      <4>E6.    @ = y'                             BY <4>1

      <4>10. outS' = y'            BY <4>0 DEF outS, y
      <4>11.     @ = A(x)          BY <4>E1, <4>E2, <4>E3, <4>E4, <4>E5, <4>E6       
      <4>12.     @ = A1step!A(x)   BY H_A1stepEqA         
      <4> QED
        BY <4>10, <4>11, <4>12
 
(*    A shorter proof, reusing the Correctness property:        

      <4>2. outS' = y'             BY <4>0 DEF outS, y
      <4>3.     @ = A(x)'          BY <2>0, <4>0 DEF Correctness        
      <4>4.     @ = A(x)           BY <4>1 DEF A, M!BigOpP, M!BigOp, M!bigOp        
      <4>5.     @ = A1step!A(x)    BY H_A1stepEqA
      <4> QED   
        BY <4>2, <4>3, <4>4, <4>5                 
*)  

    <3>D. CASE R(I0,i) /\ ~ end(I0)'
      <4>0. SUFFICES ASSUME R(I0,i),
                            ~ end(I0)'
                     PROVE  UNCHANGED <<inS,outS>>
        BY <2>0, <3>D DEF R, A1step!Next, inS                              
      <4>1. /\ ~ red(I0,i)
            /\ X' = X            
        BY <4>0 DEF R      
      <4>2. ~ end(I0)
        BY <4>1 DEF end          
      <4>3. outS  = id 
        BY <4>2 DEF outS
      <4>4. outS' = id     
        BY <4>0 DEF outS               
      <4> QED
        BY <4>1, <4>3, <4>4 DEF inS     
        
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C, <3>D 
  <2>B. CASE Done
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>> 
                   PROVE  UNCHANGED <<inS,outS>>
      BY <2>B DEF Done, vs
    <3>1. <<inS,outS>>' = <<inS,outS>> 
      BY <3>0 DEF inS, outS, vs, end
    <3> QED    
      BY <3>1
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>> 
                   PROVE  UNCHANGED <<inS,outS>>
      BY <2>C DEF vs
    <3>1. <<inS,outS>>' = <<inS,outS>>
      BY <3>0 DEF inS, outS, vs, end
    <3> QED    
      BY <3>1
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next
<1> QED 
  BY <1>1, <1>2, Thm_Inv, Thm_Correctness, PTL DEF Spec, A1step!Spec

=============================================================================
\* Modification History
\* Last modified Mon Dec 20 14:28:20 UYT 2021 by josedu
\* Last modified Thu Jul 08 02:50:17 GMT-03:00 2021 by JosEdu
\* Created Sat Jun 19 01:21:17 UYT 2021 by josedu
