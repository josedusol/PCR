------------------------- MODULE PCR_ArLeft_Thms ---------------------------

EXTENDS PCR_ArLeft, TLAPS

USE DEF Index, Assig, red

MT == INSTANCE MonoidBigOpThms
  WITH D <- D, Id <- id, \otimes <- Op 

LEMMA H_Mon == MT!Monoid(D, id, Op)
  BY H_Algebra DEF Monoid,    MT!Monoid, 
                   SemiGroup, MT!SemiGroup,
                   Magma,     MT!Magma
                   
LEMMA H_MeqMT == ASSUME NEW x, NEW y, NEW Q(_), NEW f(_)
                 PROVE  /\ M!BigOp(x,y,f)    = MT!BigOp(x,y,f)
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
          /\ i \in m..n
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
            /\ r'  = [r   EXCEPT ![I0]    = Op(@, fr(x,c[I0],i))]
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
      BY <2>0, <3>1 DEF IndexInv, TypeInv, WDIndex, wrt
    <3>3. /\ I0 \in Seq(Nat) 
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in m..n
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
      BY <2>0, <3>1 DEF IndexInv, TypeInv, WDIndex, wrt   
    <3>3. /\ I0 \in Seq(Nat) 
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in m..n
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
    <3>1. /\ c[I0][i]  = fc(x,p[I0],i)   
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
    <3>1. /\ c[I0][i]  = fc(x,p[I0],i)   
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
      BY <2>0, <3>1 DEF IndexInv, TypeInv, WDIndex, wrt   
    <3>3. /\ I0 \in Seq(Nat) 
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in m..n 
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It       
    <3>4. m \in Nat /\ n \in Nat 
      BY <2>0, <3>2, H_Type DEF TypeInv, m, n     
           
    <3>A. CASE P(I0,i)    
      <4>0. SUFFICES ASSUME P(I0,i),
                            NEW j \in It(x),
                            red(I0,j)
                     PROVE  /\ wrts(c[I0],deps(x,Dep_cr,j))
                            /\ \A k \in It(x) : k < j => red(I0,k)
        BY <2>0, <3>A DEF P, RInv1, It  
      <4>1. /\ wrts(c[I0],deps(x,Dep_cr,j)) 
            /\ \A k \in It(x) : k < j => red(I0,k)
        BY <2>0, <4>0 DEF RInv1                                               
      <4> QED 
        BY <4>1
                       
    <3>B. CASE C(I0,i)
      <4>0. SUFFICES ASSUME C(I0,i),
                            NEW j \in It(x),
                            red(I0,j)
                     PROVE  /\ wrts(c[I0]',deps(x,Dep_cr,j))
                            /\ \A k \in It(x) : k < j => red(I0,k)
        BY <2>0, <3>B DEF C, RInv1, It     
      <4>1. /\ ~ wrt(c[I0][i])
            /\ wrts(p[I0],deps(x,Dep_pc,i))
            /\ c' = [c EXCEPT ![I0][i] = fc(x,p[I0],i)] 
            /\ <<X,p>>' = <<X,p>>
        BY <4>0 DEF C        
      <4>2. \A k \in It(x) : k # i => c[I0]'[k] = c[I0][k]
        BY <4>1   
      <4>3. /\ wrts(c[I0],deps(x,Dep_cr,j))  
            /\ \A k \in It(x) : k < j => red(I0,k)
        BY <2>0, <4>0 DEF RInv1   
      <4>4. deps(x,Dep_cr,j) \subseteq It(x)
        BY <3>2, <3>3, H_Type DEF deps, It                      
      <4>5. i \notin deps(x,Dep_cr,j)
        BY <4>1, <4>3 DEF wrts              
      <4>6. /\ wrts(c[I0]',deps(x,Dep_cr,j))
            /\ \A k \in It(x) : k < j => red(I0,k)
        BY <4>2, <4>3, <4>4, <4>5 DEF wrts           
      <4> QED   
        BY <4>6   
                          
    <3>C. CASE R(I0,i)     
      <4>0. SUFFICES ASSUME R(I0,i),
                            NEW j \in It(x),
                            red(I0,j)'
                     PROVE  /\ wrts(c[I0],deps(x,Dep_cr,j))
                            /\ \A k \in It(x) : k < j => red(I0,k)'
        BY <2>0, <3>C DEF R, RInv1, It     
      <4>1. /\ ~ red(I0,i)   
            /\ wrts(c[I0],deps(x,Dep_cr,i))
            /\ i-1 >= m  =>  red(I0,i-1)
            /\ rs' = [rs EXCEPT ![I0][i] = TRUE]
            /\ <<X,c>>' = <<X,c>>            
        BY <4>0 DEF R  
      <4>2. /\ \A k \in It(x) : k # i => red(I0,k)' = red(I0,k)
            /\ red(I0,i)' 
        BY <2>0, <4>1 DEF TypeInv       
      <4>A. CASE i = j    
        <5>A. CASE i-1 >= m
          <6>1. red(I0,i-1)
            BY <4>1, <5>A
          <6>2. red(I0,i-1)'
            BY <3>3, <3>4, <4>2, <5>A, <6>1 DEF It
          <6>3. \A k \in It(x) : k < i-1 => red(I0,k)
            BY <2>0, <3>3, <3>4, <5>A, <6>1 DEF RInv1, It
          <6>4. \A k \in It(x) : k < i-1 => red(I0,k)'
            BY <4>2, <6>3 DEF It
          <6>5. \A k \in It(x) : k < i => red(I0,k)'
            BY <3>3, <3>4, <6>2, <6>4
          <6>6. wrts(c[I0],deps(x,Dep_cr,i))
            BY <4>1  
          <6> QED
            BY <4>A, <6>5, <6>6          
        <5>B. CASE i-1 < m
          <6>1. i = m /\ j = m
            BY <3>3, <3>4, <4>A, <5>B
          <6>2. red(I0,i)'
            BY <4>2  
          <6>3. \A k \in It(x) : k < i => red(I0,k)'  
            BY <3>4, <6>1, <6>2 DEF It
          <6>4. wrts(c[I0],deps(x,Dep_cr,i))
            BY <4>1  
          <6> QED
            BY <4>A, <6>3, <6>4         
        <5> QED
          BY <3>3, <3>4, <5>A, <5>B            
      <4>B. CASE i # j            
        <5>1. red(I0,j)'
          BY <4>0, <4>2, <4>B
        <5>2. red(I0,j)    
          BY <4>2, <4>B, <5>1 
        <5>3. /\ wrts(c[I0],deps(x,Dep_cr,j))
              /\ \A k \in It(x) : k < j => red(I0,k)
          BY <2>0, <5>2 DEF RInv1 
        <5>4. /\ wrts(c[I0],deps(x,Dep_cr,j))
              /\ \A k \in It(x) : k < j => red(I0,k)'
          BY <4>2, <4>B, <5>3             
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
                   PROVE  /\ wrts(c[I0],deps(x,Dep_cr,i))
                          /\ \A k \in It(x) : k < i => red(I0,k)
      BY <2>0, <2>B DEF Done, vs, RInv1, It
    <3>1. /\ wrts(c[I0],deps(x,Dep_cr,i)) 
          /\ \A k \in It(x) : k < i => red(I0,k)
      BY <2>0, <3>0 DEF RInv1
    <3> QED
      BY <3>1   
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x),
                          red(I0,i)
                   PROVE  /\ wrts(c[I0],deps(x,Dep_cr,i))
                          /\ \A k \in It(x) : k < i => red(I0,k)
      BY <2>0, <2>C DEF vs, RInv1, It
    <3>1. /\ wrts(c[I0],deps(x,Dep_cr,i)) 
          /\ \A k \in It(x) : k < i => red(I0,k)
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
           Q(i) == red(I0,i)
           f(i) == fr(x,c[I0],i)
<1>1. Init => RInv2
  <2>0. SUFFICES ASSUME Init,
                        NEW i \in It(x),
                        ~ red(I0,i)
                 PROVE  y = M!BigOpP(m,i-1,Q,f)
    BY DEF RInv2    
  <2>1. /\ I0    \in Seq(Nat)
        /\ I0    \in WDIndex 
        /\ x     \in T       
        /\ It(x) \subseteq Nat
      BY <2>0, H_Type, H_Undef DEF Init, It, WDIndex, wrt
  <2>2. M!BigOpP(m,i-1,Q,f) = id 
    <3>A. CASE m = i
      <4>1. m \in Int /\ i-1 \in Int   
        BY <2>1, <3>A, H_Type DEF m, n
      <4>2. m > i-1
        BY <3>A, <4>1 
      <4> QED
        BY <4>1, <4>2, H_Mon, H_MeqMT, MT!EmptyIntvAssumpP, Isa 
    <3>B. CASE m < i
      <4>1. m \in Nat /\ i-1 \in Nat   
        BY <2>1, <3>B, H_Type DEF m, n       
      <4>2. \A j \in m..i-1 : Q(j) \in BOOLEAN
        BY <2>1, <2>0, <4>1, H_Type, m..i-1 \subseteq Nat DEF Init, It
      <4>3. \A j \in {j \in m..i-1 : Q(j)} : f(j) \in D
        <5>1. \A j \in Nat : ~ red(I0,j)       
          BY <2>0, <2>1 DEF Init
        <5> QED
          BY <2>1, <4>1, <5>1, m..i-1 \subseteq Nat DEF It
      <4>4. \A j \in m..i-1 : ~ Q(j)              
        <5>1. \A j \in Nat : ~ red(I0,j)
          BY <2>1, <2>0 DEF Init
        <5> QED     
          BY <2>1, <4>1, <5>1   
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4, H_Mon, H_MeqMT, MT!FalsePredicate, Isa 
    <3> QED
      BY <2>1, <3>A, <3>B, H_Type DEF It   
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
          /\ i \in m..n
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It       
    <3>4. m \in Nat /\ n \in Nat 
      BY <2>0, <3>2, H_Type DEF TypeInv, m, n         
       
    <3>A. CASE P(I0,i)           
      <4>0. SUFFICES ASSUME P(I0,i),
                            NEW j \in It(x),
                            ~ red(I0,j)
                     PROVE  y = M!BigOpP(m,j-1,Q,f)
        BY <2>0, <3>A DEF P, RInv2, M!BigOpP, M!BigOp, M!bigOp     
      <4>1. y = M!BigOpP(m,j-1,Q,f) 
        BY <2>0, <4>0 DEF RInv2                  
      <4> QED 
        BY <4>1
                
    <3>B. CASE C(I0,i)   
      <4>0. SUFFICES ASSUME C(I0,i),
                            NEW j \in It(x),
                            ~ red(I0,j)
                     PROVE  y = M!BigOpP(m,j-1,Q,f)'
        BY <2>0, <3>B DEF C, RInv2, M!BigOpP, M!BigOp, M!bigOp      
      <4>1. /\ ~ wrt(c[I0][i]) 
            /\ c' = [c EXCEPT ![I0][i] = fc(x,p[I0],i)]
            /\ <<X,r,rs>>' = <<X,r,rs>>  
        BY <4>0 DEF C       
           
      <4> DEFINE fn(k) == fr(x,c[I0]',k)
                   
      <4>2. \A k \in {k \in m..j-1 : Q(k)} : f(k) \in D /\ fn(k) \in D
        <5>0. SUFFICES ASSUME NEW k \in {k \in m..j-1 : Q(k)}
                       PROVE  f(k) \in D /\ fn(k) \in D
          OBVIOUS             
        <5>1. deps(x,Dep_cr,k) \subseteq It(x)
          BY <3>2, <3>3, H_Type DEF deps, It
        <5>2. /\ It(x)' = It(x)
              /\ m' = m /\ n' = n 
              /\ m..j-1 \subseteq It(x)
          BY <3>2, <3>3, <3>4, <4>1 DEF It, m, n         
        <5>A. f(k) \in D
          <6>1. red(I0,k)  
            BY <5>0          
          <6>2. wrts(c[I0],deps(x,Dep_cr,k)) 
            BY <2>0, <5>2, <6>1 DEF RInv1, It
          <6>3. fr(x,c[I0],k) \in D    
            BY <2>0, <3>2, <3>3, <5>1, <5>2, <6>2, H_BFunWD DEF TypeInv
          <6> QED 
            BY <6>3  
        <5>B. fn(k) \in D
          <6>1. red(I0,k)'  
            BY <4>1, <5>0
          <6>2. wrts(c[I0]',deps(x,Dep_cr,k)) 
            BY <2>0, <5>2, <6>1 DEF RInv1, It, wrts, deps  
          <6>3. fr(x,c[I0]',k) \in D    
            BY <2>0, <3>2, <3>3, <5>1, <5>2, <6>2, H_BFunWD DEF TypeInv
          <6> QED 
            BY <6>3            
        <5> QED
          BY <5>A, <5>B       
      
      <4>3. \A k \in {k \in m..j-1 : Q(k)} : f(k) = fn(k)
        <5>0. SUFFICES ASSUME NEW k \in {k \in m..j-1 : Q(k)}, 
                              k \in It(x)
                       PROVE  f(k) = fn(k)
          BY <3>2, <3>3, <3>4 DEF It, m, n          
        <5>1. \A k2 \in It(x) : k2 # i => c[I0]'[k2] = c[I0][k2]
          BY <4>1
        <5>2. red(I0,k)
          BY <5>0 
        <5>3. wrts(c[I0],deps(x,Dep_cr,k))
          BY <2>0, <5>0, <5>2 DEF RInv1
        <5>4. deps(x,Dep_cr,k) \subseteq It(x)
          BY <3>2, <3>3, <5>0, H_Type DEF deps, It 
        <5>5. i \notin deps(x,Dep_cr,k)
          BY <4>1, <5>0, <5>3 DEF wrts  
        <5>6. \A k2 \in deps(x,Dep_cr,k) : 
                wrt(c[I0][k2]) /\ c[I0][k2] = c[I0]'[k2]
          BY <5>0, <5>1, <5>3, <5>4, <5>5 DEF wrts 
        <5>7. c[I0] \in St(Tc) /\ c[I0]' \in St(Tc)
          BY <2>0, <3>3 DEF TypeInv, St 
        <5> QED
          BY <3>2, <3>3, <5>0, <5>6, <5>7, H_frRelevance DEF eqs
      
      <4> HIDE DEF m, n, Q, f, fn
      
      <4>4. M!BigOpP(m,j-1,Q,f) = M!BigOpP(m,j-1,Q,fn)
        <5>A. CASE m = j
          <6>1. m \in Int /\ j-1 \in Int 
            BY <3>3, <3>4
          <6>2. m > j-1
            BY <5>A, <6>1
          <6>3. MT!BigOpP(m,j-1,Q,f)  = id
            BY <6>1, <6>2, H_Mon, H_MeqMT, MT!EmptyIntvAssumpP
          <6>4. MT!BigOpP(m,j-1,Q,fn) = id
            BY <6>1, <6>2, H_Mon, H_MeqMT, MT!EmptyIntvAssumpP
          <6> QED
            BY <6>3, <6>4, H_MeqMT          
        <5>B. CASE m < j
          <6>1. m \in Nat /\ j-1 \in Nat 
            BY <3>3, <3>4, <5>B DEF It, m, n
          <6>2. m <= j-1
            BY <3>3, <3>4, <5>B, <6>1  
          <6>3. \A k \in m..j-1 : Q(k) \in BOOLEAN    
            BY <2>0, <3>2, <3>3, <6>1 DEF TypeInv, Q
          <6>4. /\ \A k \in {k \in m..j-1 : Q(k)} : f(k)  \in D
                /\ \A k \in {k \in m..j-1 : Q(k)} : fn(k) \in D  
            BY <4>2
          <6>5. \A k \in {k \in m..j-1 : Q(k)} : f(k) = fn(k)   
            BY <4>3
          <6>6. MT!BigOpP(m,j-1,Q,f) = MT!BigOpP(m,j-1,Q,fn)  
            BY <6>1, <6>2, <6>3, <6>4, <6>5, H_Mon, MT!FunctionEqP, IsaM("blast") 
          <6> QED    
            BY <6>6, H_MeqMT    
        <5> QED
          BY <3>3, <3>4, <5>A, <5>B DEF It, m, n     
 
      <4>5. M!BigOpP(m,j-1,Q,f)' = M!BigOpP(m,j-1,Q,fn)
        <5>1. m' = m                    BY <3>3, <4>1 DEF m 
        <5>2. \A k : Q(k) <=> Q(k)      BY <4>1
        <5> QED   
          BY <4>1, <5>1, <5>2 DEF M!BigOpP,M!BigOp,M!bigOp,Q,m,n,f,fn
          
      <4>E1. y = M!BigOpP(m,j-1,Q,f)    BY <2>0, <4>0 DEF RInv2,It,Q,f,m,n
      <4>E2. @ = M!BigOpP(m,j-1,Q,fn)   BY <4>4
      <4>E3. @ = M!BigOpP(m,j-1,Q,f)'   BY <4>5
                         
      <4> QED 
        BY <4>E1, <4>E2, <4>E3   
                          
    <3>C. CASE R(I0,i) 
      <4>0. SUFFICES ASSUME R(I0,i),
                            NEW j \in It(x),
                            ~ red(I0,j)'
                     PROVE  y' = M!BigOpP(m,j-1,Q,f)'
        BY <2>0, <3>C DEF R, RInv2, It, m, n, M!BigOpP, M!BigOp, M!bigOp      
      <4>1. /\ ~ red(I0,i)    
            /\ wrts(c[I0],deps(x,Dep_cr,i))
            /\ i-1 >= m  =>  red(I0,i-1)
            /\ y'  = Op(y, f(i))     
            /\ rs' = [rs EXCEPT ![I0][i] = TRUE]
            /\ <<X,c>>' = <<X,c>>            
        BY <2>0, <4>0, <3>3 DEF TypeInv, R, St             
      <4>2. SUFFICES ASSUME i # j
                     PROVE y' = M!BigOpP(m,j-1,Q,f)'
        <5>1. ASSUME i = j
              PROVE FALSE
          <6>1. red(I0,i)'    BY <2>0, <4>1 DEF TypeInv 
          <6>2. ~ red(I0,j)'  BY <4>0 
          <6> QED       
            BY <5>1, <6>1, <6>2 
        <5> QED
          BY <5>1
      <4>3. /\ \A k \in It(x) : k # i => red(I0,k)' = red(I0,k)
            /\ ~ red(I0,j)
            /\ red(I0,i)'
        BY <2>0, <4>0, <4>1 DEF TypeInv 
        
      <4>4. /\ \A k \in {k \in m..n : Q(k)}  \union {i} : f(k) \in D   
            /\ \A k \in {k \in m..n : Q(k)'} \union {i} : f(k) \in D
        <5>A. \A k \in {k \in m..n : Q(k)} \union {i}  : f(k) \in D        
          <6>0. SUFFICES ASSUME NEW k \in {k \in m..n : Q(k)} \union {i}
                         PROVE  f(k) \in D  
            OBVIOUS             
          <6>1. deps(x,Dep_cr,k) \subseteq It(x)
            BY <3>2, <3>3, H_Type DEF deps,It
          <6>A. CASE k = i
            <7>1. wrts(c[I0],deps(x,Dep_cr,k)) 
              BY <6>A, <4>1
            <7>2. fr(x,c[I0],k) \in D    
              BY <2>0, <3>2, <3>3, <6>1, <6>A, <7>1, H_BFunWD DEF TypeInv
            <7> QED
              BY <7>2 DEF f
          <6>B. CASE k # i
            <7>1. red(I0,k)  
              BY <6>0, <6>B
            <7>2. wrts(c[I0],deps(x,Dep_cr,k)) 
              BY <2>0, <7>1 DEF RInv1, It   
            <7>3. fr(x,c[I0],k) \in D    
              BY <2>0, <3>2, <3>3, <6>1, <7>2, H_BFunWD DEF TypeInv, It 
            <7> QED  
              BY <7>3 DEF f
          <6> QED
            BY <6>A, <6>B            
        <5>B. \A k \in {k \in m..n : Q(k)'} \union {i} : f(k) \in D 
          <6>1. \A k \in {k \in m..n : Q(k)'} : f(k) \in D   
            BY <4>3, <5>A DEF It
          <6>2. fr(x,c[I0],i) \in D 
            <7>1. wrts(c[I0],deps(x,Dep_cr,i)) 
              BY <4>1              
            <7> QED   
              BY <2>0, <3>2, <3>3, <7>1, H_BFunWD DEF TypeInv   
          <6> QED 
            BY <6>1, <6>2 DEF f  
        <5> QED
          BY <5>A, <5>B
      
      <4>5. /\ j \in i+1..n
            /\ i \in m..j-1
        <5>1. red(I0,i)' 
          BY <2>0, <4>1 DEF TypeInv 
        <5>2. \A k \in It(x) : k < i => red(I0,k)' 
          BY <2>0, <4>1, <5>1 DEF RInv1, It, m, n
        <5>3. i # j
          BY <4>2  
        <5> QED
          BY <4>0, <3>2, <3>4, <5>2, <5>3 DEF It, m, n

      <4> DEFINE Qn(k)    == red(I0,k)'
                 IfQnf(k) == IF Qn(k) THEN f(k) ELSE id
      <4> HIDE DEF Q, Qn, f, m, n 

      <4>6. y = M!BigOpP(m,i-1,Q,f)
        BY <2>0, <4>1, <4>3 DEF RInv2, It, Q, f, m, n 
      
      <4>7. M!BigOpP(m,i-1,Q,f) = M!BigOpP(m,i-1,Qn,f)
        <5>A. CASE m = i
          <6>1. m \in Int /\ i-1 \in Int 
            BY <3>3, <3>4
          <6>2. m > i-1
            BY <5>A, <6>1
          <6>3. MT!BigOpP(m,i-1,Q,f)  = id
            BY <6>1, <6>2, H_Mon, H_MeqMT, MT!EmptyIntvAssumpP
          <6>4. MT!BigOpP(m,i-1,Qn,f) = id
            BY <6>1, <6>2, H_Mon, H_MeqMT, MT!EmptyIntvAssumpP
          <6> QED
            BY <6>3, <6>4, H_MeqMT
        <5>B. CASE m < i
          <6>1. m \in Nat /\ i-1 \in Nat 
            BY <3>3, <3>4, <5>B 
          <6>2. m <= i-1
            BY <3>3, <3>4, <6>1, <5>B        
          <6>3. \A k \in {k \in m..i-1 : Q(k) /\ Qn(k)} : f(k) \in D
            BY <3>4, <4>4, <4>5, <6>1, m..i-1 \subseteq m..n DEF Q, Qn, It 
          <6>4. /\ \A k \in m..i-1 : Q(k)  \in BOOLEAN  
                /\ \A k \in m..i-1 : Qn(k) \in BOOLEAN  
            BY <2>0, <3>2, <3>3, <6>1 DEF TypeInv, Q, Qn
          <6>5. \A k \in m..i-1 : Q(k) <=> Qn(k)     
            BY <3>3, <3>4, <4>3, <6>1, <6>4 DEF Q, Qn, It, m, n   
          <6>6. MT!BigOpP(m,i-1,Q,f) = MT!BigOpP(m,i-1,Qn,f)
            BY <6>1, <6>2, <6>3, <6>4, <6>5, H_Mon, MT!PredicateEq, Isa        
          <6> QED 
            BY <6>6, H_MeqMT      
        <5> QED
          BY <3>3, <3>4, <5>A, <5>B    
      
      <4>8. M!BigOpP(m,i,Qn,f) = Op(M!BigOpP(m,i-1,Qn,f), IfQnf(i))
        <5>1. m \in Nat /\ i \in Nat
          BY <3>3, <3>4
        <5>2. m <= i  
          BY <3>2, H_Type DEF It, m, n
        <5>3. \A k \in m..i : Qn(k) \in BOOLEAN    
          BY <2>0, <3>2, <3>3, <5>1 DEF TypeInv, Qn
        <5>4. \A k \in {k \in m..i : Qn(k)} : f(k) \in D 
          BY <3>4, <4>4, <4>5, <5>1, m..i \subseteq m..n DEF Q, Qn, It
        <5>5. MT!BigOpP(m,i,Qn,f) = Op(MT!BigOpP(m,i-1,Qn,f), IfQnf(i)) 
          BY <5>1, <5>2, <5>3, <5>4, H_Mon, MT!SplitLastP, Isa
        <5> QED
          BY <5>5, H_MeqMT
      
      <4>9. M!BigOpP(m,i,Qn,f) = Op(M!BigOpP(m,i,Qn,f),id)
        <5>1. m \in Nat /\ i \in Nat 
          BY <3>3, <3>4 
        <5>2. \A k \in m..i : Qn(k) \in BOOLEAN    
          BY <2>0, <3>2, <3>3, <5>1 DEF TypeInv, Qn
        <5>3. \A k \in {k \in m..i : Qn(k)} : f(k) \in D 
          BY <3>4, <4>4, <4>5, <5>1, m..i \subseteq m..n DEF Q, Qn, It  
        <5>4. M!BigOpP(m,i,Qn,f) \in D
          BY <5>1, <5>2, <5>3, H_Mon, H_MeqMT, MT!BigOpPType, Isa
        <5> QED
          BY <5>4, H_Mon, H_MeqMT, MT!OpIdentity
      
      <4>10. M!BigOpP(i+1,j-1,Qn,f) = id
        <5>1. i+1 \in Nat /\ j-1 \in Nat 
          BY <3>3, <3>4, <4>5
        <5>2. \A k \in i+1..j-1 : Qn(k) \in BOOLEAN 
          BY <2>0, <3>2, <3>3, <5>1 DEF TypeInv, Qn  
        <5>3. \A k \in {k \in i+1..j-1 : Qn(k)} : f(k) \in D  
          BY <3>4, <4>4, <4>5, <5>1, i+1..j-1 \subseteq m..n DEF Q, Qn, It          
        <5>4. \A k \in i+1..j-1 : ~ Qn(k) 
          <6>1. \A k \in i+1..n : ~ Q(k)
            <7>0. SUFFICES ASSUME NEW k \in i+1..n, Q(k)
                           PROVE FALSE
              OBVIOUS 
            <7>1. red(I0,k)  
              BY <7>0 DEF Q    
            <7>2. i+1..n \subseteq m..n
              BY <3>3, <3>4 DEF It, m, n          
            <7>3. \A k2 \in m..n : k2 < k => red(I0,k2) 
              BY <2>0, <4>1, <5>1, <7>1, <7>2 DEF RInv1, It, m, n  
            <7>4. red(I0,i)     
              BY <3>4, <5>1, <7>0, <7>2, <7>3 DEF It, m, n
            <7>5. ~ red(I0,i)
              BY <4>1          
            <7> QED
              BY <7>4, <7>5 
          <6>2. \A k \in i+1..n : ~ Qn(k)  
            BY <3>3, <3>4, <4>3, <5>1, <6>1 DEF Q, Qn, It, m, n
          <6> QED
            BY <3>3, <3>4, <4>5, <5>1, <6>2
        <5>5. MT!BigOpP(i+1,j-1,Qn,f) = id   
          BY <5>1, <5>2, <5>3, <5>4, H_Mon, MT!FalsePredicate, Isa  
        <5> QED  
          BY <5>5, H_MeqMT
            
      <4>11. M!BigOpP(m,j-1,Qn,f) = Op(M!BigOpP(m,i,Qn,f), 
                                       M!BigOpP(i+1,j-1,Qn,f))
        <5>1. m \in Nat /\ j-1 \in Nat 
          BY <3>3, <3>4, <4>5
        <5>2. m <= j-1
          BY <3>3, <3>4, <4>5, <5>1  
        <5>3. i \in m..j-1 
          BY <4>5
        <5>4. \A k \in m..j-1 : Qn(k) \in BOOLEAN 
          BY <2>0, <3>2, <3>3, <5>1 DEF TypeInv, Qn
        <5>5. \A k \in {k \in m..j-1 : Qn(k)} : f(k) \in D  
          BY <3>4, <4>4, <4>5, <5>1, m..j-1 \subseteq m..n DEF Q, Qn, It
        <5>6. MT!BigOpP(m,j-1,Qn,f) = Op(MT!BigOpP(m,i,Qn,f), 
                                         MT!BigOpP(i+1,j-1,Qn,f)) 
          BY <5>1, <5>2, <5>3, <5>4, <5>5, H_Mon, MT!SplitUpP, Isa        
        <5> QED 
          BY <5>6, H_MeqMT                         
                                       
      <4>12. M!BigOpP(m,j-1,Qn,f) = M!BigOpP(m,j-1,Q,f)'                                 
        <5>1. m' = m                       BY <4>1 DEF m
        <5>2. \A k : f(k)' = f(k)          BY <4>1 DEF f
        <5> QED   
          BY <5>1, <5>2 DEF Q, Qn, M!BigOpP, M!BigOp, M!bigOp, Isa

      <4>E1. y' = Op(y, f(i))                                    BY <4>1
      <4>E2.  @ = Op(M!BigOpP(m,i-1,Q,f), f(i))                  BY <4>6      
      <4>E3.  @ = Op(M!BigOpP(m,i-1,Qn,f), f(i))                 BY <4>7
      <4>E4.  @ = Op(M!BigOpP(m,i-1,Qn,f), IfQnf(i))             BY <4>3 DEF Qn      
      <4>E5.  @ = M!BigOpP(m,i,Qn,f)                             BY <4>8
      <4>E6.  @ = Op(M!BigOpP(m,i,Qn,f), id)                     BY <4>9      
      <4>E7.  @ = Op(M!BigOpP(m,i,Qn,f), M!BigOpP(i+1,j-1,Qn,f)) BY <4>10
      <4>E8.  @ = M!BigOpP(m,j-1,Qn,f)                           BY <4>11
      <4>E9.  @ = M!BigOpP(m,j-1,Q,f)'                           BY <4>12
        
      <4> QED      
        BY <4>E1, <4>E2, <4>E3, <4>E4, <4>E5, 
           <4>E6, <4>E7, <4>E8, <4>E9   
                        
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C         
  <2>B. CASE Done  
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x),
                          ~ red(I0,i)
                   PROVE  y = M!BigOpP(m,i-1,Q,f)
      BY <2>0, <2>B DEF Done, vs, RInv2, M!BigOpP, M!BigOp, M!bigOp
    <3>1. y = M!BigOpP(m,i-1,Q,f)    
      BY <2>0, <3>0 DEF RInv2
    <3> QED
      BY <3>1    
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x),
                          ~ red(I0,i)
                   PROVE  y = M!BigOpP(m,i-1,Q,f)
      BY <2>0, <2>C DEF vs, RInv2, M!BigOpP, M!BigOp, M!bigOp
    <3>1. y = M!BigOpP(m,i-1,Q,f)    
      BY <2>0, <3>0 DEF RInv2
    <3> QED
      BY <3>1     
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next          
<1> QED 
  BY <1>1, <1>2, Thm_IndexInv, Thm_TypeInv, Thm_RInv1, PTL DEF Spec

THEOREM Thm_Inv == Spec => []Inv
  BY Thm_IndexInv, Thm_TypeInv, Thm_PInv, Thm_CInv, 
     Thm_RInv1, Thm_RInv2, PTL DEF Inv

THEOREM Thm_Correctness == Spec => []Correctness!1
<1> DEFINE x    == X[I0]
           y    == r[I0]
           m    == lBnd(x) 
           n    == uBnd(x)
           f(i) == Fr(x,Fc(x,Gp(x)))[i]          
<1>1. Init => Correctness!1
  <2>0. SUFFICES ASSUME Init,
                        end(I0)
                 PROVE  y = A(x)
    BY DEF Correctness
  <2>1. /\ I0    \in Seq(Nat)
        /\ x     \in T    
        /\ It(x) \subseteq Nat
    BY <2>0, H_Type DEF Init, It
  <2>2. m \in Nat /\ n \in Nat   
    BY <2>1, H_Type  
  <2>A. CASE It(x) = {}
    <3>1. m > n
      BY <2>A, <2>2 DEF It, m, n 
    <3>2. A(x) = id 
      BY <2>2, <3>1, H_Mon, H_MeqMT DEF A, M!BigOp
    <3>3. y = id
      BY <2>0, <2>1 DEF Init 
    <3> QED
      BY <3>2, <3>3
  <2>B. CASE It(x) # {}
    <3>1. \A i \in It(x) : red(I0,i)        BY <2>0 DEF end   
    <3>2. \A i \in Nat : ~ red(I0,i)        BY <2>0, <2>1 DEF Init
    <3>3. FALSE                             BY <2>1, <2>B, <3>1, <3>2   
    <3> QED                                 BY <3>3
  <2> QED 
    BY <2>A, <2>B
<1>2. /\ Inv 
      /\ Correctness!1 
      /\ [Next]_<<in,vs>>
      => Correctness!1'
  <2>0. SUFFICES ASSUME IndexInv, TypeInv, PInv,
                        CInv, RInv1, RInv2,
                        Correctness!1,
                        [Next]_<<in,vs>>
                 PROVE  Correctness!1'
    BY DEF Inv 
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i) 
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE Correctness!1'
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
          /\ i \in m..n 
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
      <4>2. ~ wrt(p[I0][i]) => ~ red(I0,i )   BY <3>5
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
            /\ i-1 >= m  =>  red(I0,i-1)
            /\ y'  = Op(y, g(i))
            /\ rs' = [rs EXCEPT ![I0][i] = TRUE]
            /\ X'  = X
        BY <2>0, <4>0, <3>3 DEF TypeInv, R, St 
                
      <4>2. /\ \A j \in It(x)\{i} : red(I0,j)
            /\ \A j \in It(x) : j < i => red(I0,j)
            /\ ~ red(I0,i) 
        <5>1. It(x)' = It(x)           
          BY <4>1 DEF It, m, n    
        <5>2. ~ red(I0,i)
          BY <4>1
        <5>3. rs' = [rs EXCEPT ![I0][i] = TRUE]
          BY <4>1                 
        <5>4. \A j \in It(x) : red(I0,j)'
          BY <4>0, <5>1 DEF end
        <5>5. \A j \in It(x)\{i} : red(I0,j)  
          BY <5>2, <5>3, <5>4
        <5>6. \A j \in It(x) : j < i => red(I0,j)
          BY <5>5 DEF It             
        <5> QED 
          BY <5>2, <5>5, <5>6     
           
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

      <4>7. i = n
        <5>0. SUFFICES ASSUME i # n
                       PROVE FALSE
          OBVIOUS                  
        <5>1. \A j \in It(x)\{i} : red(I0,j) 
          BY <4>2
        <5>2. red(I0,n)
          BY <3>2, <3>3, <5>0, <5>1, H_Type DEF It
        <5>3. \A j \in It(x) : j < n => red(I0,j)   
          BY <2>0, <3>2, <3>3, <5>2, H_Type DEF RInv1, It
        <5>4. i < n
          BY <3>2, <5>0, H_Type DEF It
        <5>5. red(I0,i)
          BY <5>0, <5>1, <5>3, <5>4 DEF It
        <5>6. ~ red(I0,i)    
          BY <4>2 
        <5> QED 
          BY <5>5, <5>6
          
      <4> DEFINE Q(j)    == red(I0,j)
                 IfQg(j) == IF Q(j) THEN g(j) ELSE id
      <4> HIDE DEF Q, f, g, m, n    
                            
      <4>8. M!BigOp(m,n,f) = Op(M!BigOp(m,n-1,f), f(n))                  
        <5>1. m \in Nat /\ n \in Nat
          BY <3>4 
        <5>2. m <= n  
          BY <3>2, H_Type DEF It, m, n
        <5>3. \A j \in m..n : f(j) \in D
          BY <4>6 DEF It, m, n
        <5>4. MT!BigOp(m,n,f) = Op(MT!BigOp(m,n-1,f), f(n)) 
          BY <5>1, <5>2, <5>3, H_Mon, MT!SplitLast, Isa
        <5> QED
          BY <5>4, H_MeqMT

      <4>9. M!BigOp(m,n-1,f) = M!BigOpP(m,n-1,Q,f)
        <5>A. CASE m = n
          <6>1. m \in Int /\ n-1 \in Int 
            BY <3>3, <3>4
          <6>2. m > n-1
            BY <5>A, <6>1
          <6>3. MT!BigOp(m,n-1,f) = id
            BY <6>1, <6>2, H_Mon, H_MeqMT DEF MT!BigOp
          <6>4. MT!BigOpP(m,n-1,Q,f) = id
            BY <6>1, <6>2, H_Mon, H_MeqMT, MT!EmptyIntvAssumpP
          <6> QED
            BY <6>3, <6>4, H_MeqMT                    
        <5>B. CASE m < n               
          <6>1. m \in Nat /\ n-1 \in Nat
            BY <3>4, <5>B 
          <6>2. \A j \in m..n-1 : Q(j) \in BOOLEAN    
            BY <2>0, <3>2, <3>3, <6>1 DEF TypeInv, Q
          <6>3. \A j \in {k \in m..n-1 : Q(k)} : f(j) \in D 
            BY <3>4, <4>6 DEF It, m, n                
          <6>4. \A j \in m..n-1 : Q(j)
            <7>1. \A j \in It(x) : j < n => red(I0,j)
              BY <4>2, <4>7              
            <7> QED
              BY <7>1, <4>7 DEF Q, It, m, n
          <6>5. MT!BigOp(m,n-1,f) = MT!BigOpP(m,n-1,Q,f)
            BY <6>1, <6>2, <6>3, <6>4, H_Mon, MT!TruePredicate, Isa
          <6> QED
            BY <6>5, H_MeqMT
        <5> QED
          BY <3>3, <3>4, <5>A, <5>B    
                         
      <4>10. /\ M!BigOpP(m,n-1,Q,f) = M!BigOpP(m,n-1,Q,g) 
             /\ f(n) = g(n) 
        <5>1. M!BigOpP(m,n-1,Q,f) = M!BigOpP(m,n-1,Q,g)           
          <6>A. CASE m = n
            <7>1. m \in Int /\ n-1 \in Int 
              BY <3>3, <3>4
            <7>2. m > n-1
              BY <6>A, <7>1
            <7>3. MT!BigOpP(m,n-1,Q,f) = id
              BY <7>1, <7>2, H_Mon, H_MeqMT, MT!EmptyIntvAssumpP
            <7>4. MT!BigOpP(m,n-1,Q,g) = id
              BY <7>1, <7>2, H_Mon, H_MeqMT, MT!EmptyIntvAssumpP   
            <7> QED
              BY <7>3, <7>4, H_MeqMT                   
          <6>B. CASE m < n              
            <7>1. m \in Nat /\ n-1 \in Nat 
              BY <3>4, <6>B 
            <7>2. \A j \in m..n-1 : Q(j) \in BOOLEAN    
              BY <2>0, <3>2, <3>3, <7>1 DEF TypeInv, Q
            <7>3. /\ \A j \in {j \in m..n-1 : Q(j)} : f(j) \in D
                  /\ \A j \in {j \in m..n-1 : Q(j)} : g(j) \in D  
              BY <3>2, <4>6, <4>7 DEF Q, It, m, n
            <7>4. \A j \in {j \in m..n-1 : Q(j)} : f(j) = g(j)   
              BY <3>3, <4>6, <4>7 DEF Q, It, m, n 
            <7>5. MT!BigOpP(m,n-1,Q,f) = MT!BigOpP(m,n-1,Q,g)  
              BY <7>1, <7>2, <7>3, <7>4, H_Mon, MT!FunctionEqP, IsaM("blast") 
            <7> QED    
              BY <7>5, H_MeqMT
          <6> QED 
            BY <3>3, <3>4, <6>A, <6>B    
        <5>2. f(n) = g(n) 
          BY <4>6, <4>7       
        <5> QED
          BY <5>1, <5>2             

      <4>11. y = M!BigOpP(m,n-1,Q,g)
        <5>1. ~ red(I0,n)
          BY <4>2, <4>7
        <5> QED 
          BY <2>0, <3>3, <4>7, <5>1 DEF RInv2, Q, g, m, n

      <4>E1. A(x) = M!BigOp(m,n,f)                      BY DEF A, f, m, n 
      <4>E2.    @ = Op(M!BigOp(m,n-1,f), f(n))          BY <4>8        
      <4>E3.    @ = Op(M!BigOpP(m,n-1,Q,f), f(n))       BY <4>9  
      <4>E4.    @ = Op(M!BigOpP(m,n-1,Q,g), g(n))       BY <4>10
      <4>E5.    @ = Op(y, g(n))                         BY <4>11
      <4>E6.    @ = y'                                  BY <4>1, <4>7       
      
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

THEOREM Thm_Refinement == Spec => PCR_A!Spec
<1> DEFINE x == X[I0]
           m == lBnd(x) 
           n == uBnd(x)
<1> USE DEF PCR_A!Index, PCR_A!Assig, PCR_A!red
<1>1. Init => PCR_A!Init 
  BY H_Type DEF Init, PCR_A!Init, Undef, PCR_A!Undef, inS
<1>2. /\ Inv 
      /\ [Next]_<<in,vs>> 
      => [PCR_A!Next]_<<inS,PCR_A!vs>>
  <2>0. SUFFICES ASSUME IndexInv, TypeInv,
                        [Next]_<<in,vs>>
                 PROVE  [PCR_A!Next]_PCR_A!vs
    BY DEF Inv, inS, PCR_A!vs
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i) 
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE [PCR_A!Next]_PCR_A!vs
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
          /\ i \in m..n
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, H_Type DEF IndexInv, WDIndex, It       
    <3>4. m \in Nat /\ n \in Nat 
      BY <2>0, <3>2, H_Type DEF TypeInv, m, n   
    <3>5. /\ I0 \in PCR_A!WDIndex
          /\ i  \in PCR_A!It(x) 
      BY <3>3 DEF WDIndex, It, wrt, Undef, PCR_A!WDIndex, 
         PCR_A!It, PCR_A!wrt, PCR_A!Undef, propS      

    <3>A. CASE P(I0,i)    
      <4>0. SUFFICES ASSUME P(I0,i)
                     PROVE  PCR_A!P(I0,i)
         BY <2>0, <3>5, <3>A DEF P, inS, PCR_A!Next, PCR_A!Step                 
      <4> QED 
        BY <4>0 DEF P, wrt, wrts, deps, Undef, PCR_A!P, 
           PCR_A!wrt, PCR_A!wrts, PCR_A!deps, PCR_A!Undef  
    
    <3>B. CASE C(I0,i)
      <4>0. SUFFICES ASSUME C(I0,i)
                     PROVE  PCR_A!C(I0,i)
        BY <2>0, <3>5, <3>B DEF C, inS, PCR_A!Next, PCR_A!Step                     
      <4> QED 
        BY <4>0 DEF C, wrt, wrts, deps, Undef, PCR_A!C, 
           PCR_A!wrt, PCR_A!wrts, PCR_A!deps, PCR_A!Undef    

    <3>C. CASE R(I0,i)
      <4>0. SUFFICES ASSUME R(I0,i)
                     PROVE  PCR_A!R(I0,i)
        BY <2>0, <3>5, <3>C DEF R, inS, PCR_A!Next, PCR_A!Step      
      <4> QED
        BY <4>0 DEF R, wrt, wrts, deps, Undef, PCR_A!R,
           PCR_A!wrt, PCR_A!wrts, PCR_A!deps, PCR_A!Undef         
       
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C
  <2>B. CASE Done
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>> 
                   PROVE  UNCHANGED PCR_A!vs
      BY <2>B DEF Done, vs
    <3>1. PCR_A!vs' = PCR_A!vs
      BY <3>0 DEF PCR_A!vs, vs, end
    <3> QED    
      BY <3>1
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>> 
                   PROVE  UNCHANGED PCR_A!vs
      BY <2>C DEF vs
    <3>1. PCR_A!vs' = PCR_A!vs
      BY <3>0 DEF PCR_A!vs, vs, end
    <3> QED    
      BY <3>1
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next
<1> QED 
  BY <1>1, <1>2, Thm_Inv, PTL DEF Spec, PCR_A!Spec

============================================================================
\* Modification History
\* Last modified Thu Aug 19 01:24:47 UYT 2021 by josedu
\* Last modified Thu Jul 08 03:53:05 GMT-03:00 2021 by JosEdu
\* Created Thu Jun 24 21:22:42 UYT 2021 by josedu
