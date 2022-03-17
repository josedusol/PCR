------------------------ MODULE PCR_FibPrimes1_Thms ------------------------

EXTENDS PCR_FibPrimes1, PCR_FibPrimes1_Lems

USE DEF Index, Assig, Lem_Algebra, Lem_Type, Lem_BFunWD, 
        Lem_fpRelevance, Lem_fcRelevance, Lem_frRelevance

THEOREM Thm_IndexInv_FP1 == Spec => []IndexInv
  BY Thm_IndexInv, H_Type, H_BFunType_FP1, H_BFunWD, H_Algebra,
     H_fpRelevance, H_fcRelevance, H_frRelevance, PTL
     
THEOREM Thm_TypeInv_FP1 == Spec => []TypeInv
  BY Thm_TypeInv, H_Type, H_BFunType_FP1, H_BFunWD, H_Algebra,
     H_fpRelevance, H_fcRelevance, H_frRelevance, PTL
     
THEOREM Thm_PInv_FP1 == Spec => []PInv
  BY Thm_PInv, H_Type, H_BFunType_FP1, H_BFunWD, H_Algebra,
     H_fpRelevance, H_fcRelevance, H_frRelevance, PTL           

THEOREM Thm_ProdEqInv == Spec => []ProdEqInv
<1> DEFINE x == X[I0]
           m == lBnd(X[I0]) 
           n == uBnd(X[I0])
<1>1. Init => ProdEqInv
  <2>0. SUFFICES ASSUME Init,
                        NEW i \in It(x),
                        wrt(p[I0][i])
                 PROVE  FALSE
    BY DEF ProdEqInv
  <2>1. /\ I0    \in Seq(Nat) 
        /\ x     \in Nat      
        /\ It(x) \subseteq Nat
        /\ i     \in Nat 
    BY <2>0, Lem_Type DEF Init, It, deps, T 
  <2>2. ~ wrt(p[I0][i])  
    BY <2>0, <2>1 DEF Init, wrt   
  <2>3. FALSE    
    BY <2>0, <2>2   
  <2> QED  
    BY <2>3
<1>2. /\ IndexInv /\ TypeInv /\ TypeInv' /\ PInv /\ PInv'
      /\ ProdEqInv 
      /\ [Next]_<<in,vs>>
      => ProdEqInv'
  <2>0. SUFFICES ASSUME IndexInv, TypeInv, TypeInv', PInv, PInv',
                        ProdEqInv,
                        [Next]_<<in,vs>>
                 PROVE  ProdEqInv'
    OBVIOUS
  <2>A. CASE Step
    <3>0. SUFFICES ASSUME \E i \in It(x) : \/ P(I0,i) 
                                           \/ C(I0,i)
                                           \/ R(I0,i)
                   PROVE  ProdEqInv'
      BY <2>0, <2>A, Lem_Type DEF Step, IndexInv
    <3>1. PICK i \in It(x) : \/ P(I0,i)
                             \/ C(I0,i)
                             \/ R(I0,i)
      BY <3>0 
    <3>2. x \in Nat
      BY <2>0, <3>1 DEF IndexInv, TypeInv, WDIndex, wrt, T
    <3>3. /\ I0 \in Seq(Nat) 
          /\ I0 \in WDIndex
          /\ i \in Nat
          /\ i \in {k \in m..n : prop(k)} 
          /\ It(x) \subseteq Nat
      BY <2>0, <3>2, Lem_Type DEF IndexInv, WDIndex, It, T
      
    <3>A. CASE P(I0,i)    
      <4>0. SUFFICES ASSUME P(I0,i),
                            NEW j \in It(x), 
                            wrt(p[I0][j])'
                     PROVE  fp(x,p[I0],j)' = gp(x,j)
         BY <2>0, <3>A DEF P, ProdEqInv, It   
      <4>1. /\ ~ wrt(p[I0][i])
            /\ wrts(p[I0],deps(x,Dep_pp,i)\{i})
            /\ p' = [p EXCEPT ![I0][i] = fp(x,p[I0],i)] 
            /\ X' = X
        BY <4>0 DEF P          
      <4>A. CASE j <= 2  
        BY <3>3, <4>A, fibonacciDef DEF fp, fibs, gp          
      <4>B. CASE j > 2 /\ i = j
        <5>1. /\ i-1 \in It(x)
              /\ i-2 \in It(x) 
              /\ i-1 \in deps(x,Dep_pp,i)\{i}
              /\ i-2 \in deps(x,Dep_pp,i)\{i}
          BY <3>2, <3>3, <4>B DEF It, deps, Dep_pp, lBnd, uBnd, prop  
        <5>2. /\ wrt(p[I0][i-1])
              /\ wrt(p[I0][i-2])
          BY <3>3, <2>0, <4>1, <4>B, <5>1 DEF wrts
        <5>3. /\ fp(x,p[I0],i-1) = gp(x,i-1)   
              /\ fp(x,p[I0],i-2) = gp(x,i-2)   
          BY <2>0, <3>3, <4>B, <5>1, <5>2 DEF ProdEqInv
        <5>4. /\ p[I0][i-1] = fp(x,p[I0],i-1)  
              /\ p[I0][i-2] = fp(x,p[I0],i-2) 
          BY <2>0, <3>3, <4>B, <5>1, <5>2 DEF PInv
        <5>5. /\ p[I0][i-1] = gp(x,i-1)
              /\ p[I0][i-2] = gp(x,i-2)  
          BY <5>3, <5>4 
        <5>E1. fp(x,p[I0],i)' = p[I0][i-1] + p[I0][i-2]  BY <3>3, <4>1, <4>B DEF fp, fibs 
        <5>E2.              @ = gp(x,i-1) + gp(x,i-2)    BY <5>5
        <5>E3.              @ = gp(x,i)                  BY <3>3, <4>B, fibonacciDef DEF gp       
        <5> QED
          BY <4>B, <5>E1, <5>E2, <5>E3        
      <4>C. CASE j > 2 /\ i # j 
        <5>1. \A k \in It(x) : k # i => p[I0][k]' = p[I0][k]
          BY <4>1
        <5>2. p[I0][j]' = p[I0][j]  
          BY <4>C, <5>1
        <5>3. wrt(p[I0][j])    
          BY <4>0, <5>2 DEF wrt     
        <5>4. fp(x,p[I0],j) = gp(x,j)
          BY <2>0, <5>3 DEF ProdEqInv 
        <5>5. wrts(p[I0],deps(x,Dep_pp,j)) 
          BY <2>0, <5>3 DEF PInv        
        <5>6. wrts(p[I0],deps(x,Dep_pp,j)\{j}) 
          BY <5>5 DEF wrts, deps         
        <5>7. deps(x,Dep_pp,j) \subseteq It(x)
          BY <3>2, <3>3, Lem_Type DEF deps, It, T                      
        <5>8. i \notin deps(x,Dep_pp,j)\{j}
          BY <4>1, <5>6 DEF wrts           
        <5>9. \A k \in deps(x,Dep_pp,j)\{j} :
                wrt(p[I0][k]) /\ p[I0][k] = p[I0]'[k]
          BY <5>1, <5>6, <5>7, <5>8 DEF wrts         
        <5>10. p[I0] \in St(Nat) /\ p[I0]' \in St(Nat)
          BY <2>0, <3>3 DEF TypeInv, St, Tp          
        <5>11. fp(x,p[I0],j) = fp(x,p[I0]',j) 
          BY <3>2, <3>3, <5>9, <5>10, Lem_fpRelevance DEF eqs, Tp, T   
        <5> QED
          BY <4>1, <5>4, <5>11  
      <4> QED 
        BY <3>3, <4>A, <4>B, <4>C          
              
    <3>B. CASE C(I0,i)
      <4>0. SUFFICES ASSUME C(I0,i),
                            NEW j \in It(x), 
                            wrt(p[I0][j])
                     PROVE  fp(x,p[I0],j) = gp(x,j)
        BY <2>0, <3>B DEF C, ProdEqInv, It 
      <4>1. fp(x,p[I0],j) = gp(x,j)
        BY <2>0, <4>0 DEF ProdEqInv                 
      <4> QED 
        BY <4>1
              
    <3>C. CASE R(I0,i)     
      <4>0. SUFFICES ASSUME R(I0,i),
                            NEW j \in It(x), 
                            wrt(p[I0][j])
                     PROVE  fp(x,p[I0],j) = gp(x,j)
        BY <2>0, <3>C DEF R, ProdEqInv, It 
      <4>1. fp(x,p[I0],j) = gp(x,j)
        BY <2>0, <4>0 DEF ProdEqInv                 
      <4> QED 
        BY <4>1 
              
    <3> QED
      BY <3>1, <3>A, <3>B, <3>C         
  <2>B. CASE Done  
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x), 
                          wrt(p[I0][i])
                   PROVE  fp(x,p[I0],i) = gp(x,i)
      BY <2>0, <2>B DEF Done, vs, ProdEqInv, It
    <3>1. fp(x,p[I0],i) = gp(x,i)
      BY <2>0, <3>0 DEF ProdEqInv
    <3> QED
      BY <3>1
  <2>C. CASE UNCHANGED <<in,vs>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs>>,
                          NEW i \in It(x), 
                          wrt(p[I0][i])
                   PROVE  fp(x,p[I0],i) = gp(x,i)
      BY <2>0, <2>C DEF vs, ProdEqInv, It
    <3>1. fp(x,p[I0],i) = gp(x,i)
      BY <2>0, <3>0 DEF ProdEqInv
    <3> QED
      BY <3>1  
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C DEF Next            
<1> QED      
  BY <1>1, <1>2, Thm_IndexInv_FP1, Thm_TypeInv_FP1, Thm_PInv_FP1, PTL DEF Spec 

============================================================================
\* Modification History
\* Last modified Fri Mar 11 19:20:27 UYT 2022 by josedu
\* Last modified Wed Jul 07 17:17:17 GMT-03:00 2021 by JosEdu
\* Created Sun Jul 04 20:40:25 GMT-03:00 2021 by JosEdu
