------------------------------ MODULE Theorems ------------------------------

EXTENDS MainPCRFibPrimes1, TLAPS


ASSUME Fun_Assumptions == 
  /\ \A x, p, i : PCR1!fib(x, p, i)     \in VarPType1     
  /\ \A x, p, i : PCR1!isPrime(x, p, i) \in VarCType1
  /\ \A a, b :    PCR1!sum(a, b)        \in VarRType1   

ASSUME Bnd_Assumptions == 
  /\ \A x : PCR1!LowerBnd(x) \in IndexType1
  /\ \A x : PCR1!UpperBnd(x) \in IndexType1
  /\ \A j : PCR1!Step(j)     \in IndexType1

LEMMA Type_iterator == \A i \in PCR1!CtxIndex : PCR1!Iterator(i) \subseteq IndexType1                    


THEOREM Thm1_TypeInv == Spec => []TypeInv
<1>1. Init => TypeInv
  <2> SUFFICES ASSUME Init
               PROVE  TypeInv
    OBVIOUS
  <2>1. N \in InType1
    BY DEF Init
  <2>2. map1 \in PCR1!CtxMap
    <3>1. PCR1!InitCtx(N) \in (PCR1!CtxType \cup {NULL}) 
      BY <2>1, Bnd_Assumptions DEF PCR1!InitCtx, PCR1!CtxType, PCR1!VarP, PCR1!VarC,
                                   PCR1!States, VarRType1, IndexType1
    <3> QED 
      BY <3>1 DEF Init, PCR1!CtxMap
  <2> QED
    BY <2>1, <2>2 DEF TypeInv
<1>2. TypeInv /\ [Next]_vars => TypeInv'
  <2>0. SUFFICES ASSUME TypeInv,
                        [Next]_vars
                 PROVE  TypeInv'
    OBVIOUS
  <2>1. CASE \E i \in CtxIdType1 : Next1(i)
    <3>0. SUFFICES ASSUME NEW i \in CtxIdType1,
                          Next1(i)
                   PROVE  TypeInv'
      BY <2>1 DEF Next1
    <3>1. map1 \in PCR1!CtxMap      BY <2>0 DEF TypeInv
    <3>2. map1[i] # NULL            BY <3>0 DEF Next1
    <3>3. map1[i] \in PCR1!CtxType  BY <3>1, <3>2 DEF PCR1!CtxMap 
    <3>A. CASE /\ PCR1!State(i) = "OFF"
               /\ PCR1!Start(i)
      <4>1. N' \in InType1 BY <2>0, <3>0 DEF TypeInv, Next1     
      <4>2. map1' \in PCR1!CtxMap                                    
        <5>1. map1' = [map1 EXCEPT ![i].ste = "RUN"] BY <3>A DEF PCR1!Start
        <5>2. map1[i].ste' \in PCR1!States BY <3>3, <5>1 DEF PCR1!States, PCR1!CtxType      
        <5>3. map1[i]' \in PCR1!CtxType BY <3>2, <3>3, <5>1, <5>2 DEF PCR1!CtxType
        <5> QED 
          BY <3>1, <5>1, <5>3 DEF PCR1!CtxType, PCR1!CtxMap
      <4> QED 
        BY <4>1, <4>2 DEF TypeInv        
    <3>B. CASE /\ PCR1!State(i) = "RUN"
               /\ PCR1!P(i)
      <4>1. N' \in InType1 BY <2>0, <3>0 DEF TypeInv, Next1     
      <4>2. map1' \in PCR1!CtxMap 
        <5>1. map1' = [map1 EXCEPT 
                ![i].v_p[map1[i].i_p] = [v |-> PCR1!fib(PCR1!in(i), PCR1!v_p(i), map1[i].i_p), 
                                         r |-> 0],
                ![i].i_p = map1[i].i_p + 1]  
          BY <3>B DEF PCR1!P, PCR1!Step, PCR1!i_p
        <5>2. map1[i].i_p \in IndexType1 BY <3>3 DEF PCR1!CtxType              
        <5>3. map1[i].i_p' \in IndexType1
          <6>1. map1[i].i_p' = map1[i].i_p + 1 BY <3>1, <5>1 DEF PCR1!CtxMap, PCR1!CtxType
          <6> QED 
            BY <5>2, <6>1 DEF IndexType1
        <5>4. map1[i].v_p' \in PCR1!VarP
          <6> DEFINE j == map1[i].i_p
          <6>1. map1[i].v_p' = [map1[i].v_p EXCEPT ![j] = [v |-> PCR1!fib(PCR1!in(i), PCR1!v_p(i), j), r |-> 0]] 
            BY <3>1, <5>1 DEF PCR1!CtxMap, PCR1!CtxType
          <6>2. j \in IndexType1 BY <5>2                  
          <6> HIDE DEF j
       \* <6>3. map1[i].v_p[j]' = [v |-> PCR1!fib(PCR1!in(i), PCR1!v_p(i), j), r |-> 0]
       \*   BY <3>3, <5>2, <6>1 DEF PCR1!CtxType, PCR1!VarP   
          <6>4. PCR1!fib(PCR1!in(i), PCR1!v_p(i), j) \in VarPType1 
            BY Fun_Assumptions DEF VarPType1           
          <6> QED
            BY <3>3, <6>1, <6>2, <6>4 DEF PCR1!CtxType, PCR1!VarP  
        <5>5. map1[i]' \in PCR1!CtxType 
          BY <3>1, <3>2, <5>1, <5>3, <5>4 DEF PCR1!CtxMap, PCR1!CtxType
        <5> QED 
          BY <3>1, <5>1, <5>5 DEF PCR1!CtxType, PCR1!CtxMap            
      <4> QED 
        BY <4>1, <4>2 DEF TypeInv               
    <3>C. CASE /\ PCR1!State(i) = "RUN"
               /\ PCR1!C(i)
      <4>1. N' \in InType1 BY <2>0, <3>0 DEF TypeInv, Next1     
      <4>2. map1' \in PCR1!CtxMap 
        <5>1. PICK j \in PCR1!Iterator(i) :
                map1' = [map1 EXCEPT 
                  ![i].v_p[j].r = 1, 
                  ![i].v_c[j]   = [v |-> PCR1!isPrime(PCR1!in(i), PCR1!v_p(i), j), r |-> 0]]
          BY <3>C DEF PCR1!C
        <5>2. j \in IndexType1  BY <3>2, Type_iterator DEF PCR1!CtxIndex
        <5>3. map1[i].v_p' \in PCR1!VarP 
          <6>1. map1[i].v_p' = [map1[i].v_p EXCEPT ![j] = [map1[i].v_p[j] EXCEPT !.r = 1]] 
            BY <3>1, <5>1 DEF PCR1!CtxMap, PCR1!CtxType
          <6>2. map1[i].v_p[j].r' = 1 
            BY <3>3, <5>2, <6>1 DEF PCR1!CtxType, PCR1!VarP
          <6>3. map1[i].v_p[j].r' \in Nat BY <6>2
          <6> QED 
            BY <3>3, <5>2, <6>1, <6>3 DEF PCR1!CtxType, PCR1!VarP        
        <5>4. map1[i].v_c' \in PCR1!VarC
          <6>1. map1[i].v_c' = [map1[i].v_c EXCEPT ![j] = [v |-> PCR1!isPrime(PCR1!in(i), PCR1!v_p(i), j), r |-> 0]] 
            BY <3>1, <5>1 DEF PCR1!CtxMap, PCR1!CtxType
          <6>2. map1[i].v_c[j]' = [v |-> PCR1!isPrime(PCR1!in(i), PCR1!v_p(i), j), r |-> 0] 
            BY <3>3, <5>2, <6>1 DEF PCR1!CtxType, PCR1!VarC
          <6>3. PCR1!isPrime(PCR1!in(i), PCR1!v_p(i), j) \in VarCType1 
            BY Fun_Assumptions DEF VarCType1
          <6> QED
             BY <3>3, <5>2, <6>1, <6>3 DEF PCR1!CtxType, PCR1!VarC             
        <5>5. map1[i]' \in PCR1!CtxType 
          BY <3>1, <3>2, <5>1, <5>3, <5>4 DEF PCR1!CtxMap, PCR1!CtxType       
        <5> QED 
          BY <3>1, <5>1, <5>5 DEF PCR1!CtxType, PCR1!CtxMap         
      <4> QED BY <4>1, <4>2 DEF TypeInv                  
    <3>D. CASE /\ PCR1!State(i) = "RUN"
               /\ PCR1!R(i) 
      <4>1. N' \in InType1 BY <2>0, <3>0 DEF TypeInv, Next1     
      <4>2. map1' \in PCR1!CtxMap 
        <5>1. PICK j \in PCR1!Iterator(i) : 
                map1' = [map1 EXCEPT 
                  ![i].ret      = PCR1!sum(map1[i].ret, PCR1!v_c(i)[j].v),
                  ![i].v_c[j].r = map1[i].v_c[j].r + 1,
                  ![i].ste      = IF PCR1!CDone(i, j) THEN "END" ELSE map1[i].ste]
          BY <3>D DEF PCR1!R
        <5>2. j \in IndexType1  BY <3>2, Type_iterator DEF PCR1!CtxIndex    
        <5>3. map1[i].ret' \in VarRType1
          <6>1. map1[i].ret' = PCR1!sum(map1[i].ret, PCR1!v_c(i)[j].v) 
            BY <3>1, <5>1 DEF PCR1!CtxMap, PCR1!CtxType
          <6>2. PCR1!sum(map1[i].ret, PCR1!v_c(i)[j].v) \in VarRType1 
            BY Fun_Assumptions DEF VarRType1
          <6> QED BY <6>1, <6>2
        <5>4. map1[i].v_c' \in PCR1!VarC
          <6>1. map1[i].v_c' = [map1[i].v_c EXCEPT ![j] = [map1[i].v_c[j] EXCEPT !.r = map1[i].v_c[j].r + 1]] 
            BY <3>1, <5>1 DEF PCR1!CtxMap, PCR1!CtxType
          <6>2. map1[i].v_c[j].r' = map1[i].v_c[j].r + 1  
            BY <3>3, <5>2, <6>1 DEF PCR1!CtxType, PCR1!VarC
          <6>3. map1[i].v_c[j].r \in Nat 
            BY <3>3, <5>2 DEF PCR1!CtxMap, PCR1!CtxType, PCR1!VarC
          <6>4. map1[i].v_c[j].r' \in Nat 
            BY <6>2, <6>3
          <6> QED
            BY <3>3, <5>2, <6>1, <6>4 DEF PCR1!CtxType, PCR1!VarC
        <5>5. map1[i].ste' \in PCR1!States
          <6>1. map1[i].ste' = IF PCR1!CDone(i, j) THEN "END" ELSE map1[i].ste 
            BY <3>1, <5>1 DEF PCR1!CtxMap, PCR1!CtxType
          <6>A. CASE PCR1!CDone(i, j) 
            <7>1. map1[i].ste' = "END" BY <6>1, <6>A
            <7>2. "END" \in PCR1!States BY DEF PCR1!States           
            <7> QED BY <7>1, <7>2
          <6>B. CASE ~ PCR1!CDone(i, j) 
            <7>1. map1[i].ste' = map1[i].ste BY <6>1, <6>B
            <7>2. map1[i].ste \in PCR1!States BY <3>3 DEF PCR1!CtxMap, PCR1!CtxType         
            <7> QED BY <7>1, <7>2          
          <6> QED BY <6>A, <6>B
        <5>6. map1[i]' \in PCR1!CtxType 
          BY <3>1, <3>2, <5>1, <5>3, <5>4, <5>5 DEF PCR1!CtxMap, PCR1!CtxType 
        <5> QED 
          BY <3>1, <5>1, <5>6 DEF PCR1!CtxType, PCR1!CtxMap
      <4> QED BY <4>1, <4>2 DEF TypeInv                      
    <3>E. CASE /\ PCR1!State(i) = "RUN"
               /\ PCR1!Quit(i) 
      <4>1. N' \in InType1 BY <2>0, <3>0 DEF TypeInv, Next1     
      <4>2. map1' \in PCR1!CtxMap                                    
        <5>1. map1' = [map1 EXCEPT ![i].ste = "END"] BY <3>E DEF PCR1!Quit
        <5>2. map1[i].ste' \in PCR1!States BY <3>3, <5>1 DEF PCR1!States, PCR1!CtxType      
        <5>3. map1[i]' \in PCR1!CtxType BY <3>2, <3>3, <5>1, <5>2 DEF PCR1!CtxType
        <5> QED 
          BY <3>1, <5>1, <5>3 DEF PCR1!CtxType, PCR1!CtxMap
      <4> QED 
        BY <4>1, <4>2 DEF TypeInv                                                              
    <3> QED
      BY <3>0, <3>A, <3>B, <3>C, <3>D, <3>E DEF Next1, PCR1!Next
  <2>2. CASE Done
    <3>1. /\ N'    \in InType1
          /\ map1' \in PCR1!CtxMap  BY <2>0, <2>2 DEF Done, TypeInv, vars
    <3> QED 
      BY <3>1 DEF TypeInv
  <2>3. CASE UNCHANGED vars
    <3>1. /\ N'    \in InType1
          /\ map1' \in PCR1!CtxMap  BY <2>0, <2>3 DEF TypeInv, vars    
    <3> QED 
      BY <3>1 DEF TypeInv
  <2> QED
    BY <2>0, <2>1, <2>2, <2>3 DEF Next
<1> QED 
  BY <1>1, <1>2, PTL DEF Spec    

THEOREM Thm2_Correctness == 
  \A n \in InType1 : /\ N = n 
                     /\ Spec 
                     => [](PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(n))
  PROOF OMITTED 

THEOREM Thm3_Termination == 
  \A n \in InType1 : /\ N = n 
                     /\ FairSpec 
                     => Termination
  PROOF OMITTED 

=============================================================================
\* Modification History
\* Last modified Sat Sep 19 15:40:57 UYT 2020 by josedu
\* Created Tue Sep 08 23:52:38 UYT 2020 by josedu
