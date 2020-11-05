------------------------------ MODULE Theorems ------------------------------

VARIABLES N, map1, ip1

INSTANCE TLAPS
INSTANCE MainPCRFibPrimes1

USE DEF Undef, IndexType1, CtxIdType1, InType1, VarPType1, VarCType1, VarRType1

LEMMA Lem_IteratorType1 == Spec => []IteratorType1
  OMITTED

LEMMA Lem_IteratorType2 == Spec => []IteratorType2
  OMITTED

LEMMA Lem_ProducerType == Spec => []ProducerType
  OMITTED

LEMMA Lem_fibType == 
  ASSUME NEW x \in Nat,
         NEW p \in PCR1!VarP,
         NEW i \in Nat,
         i >= 2 => p[i - 1].v \in Nat,
         i >= 2 => p[i - 2].v \in Nat   
  PROVE PCR1!fib(x, p, i) \in Nat
  BY DEF PCR1!fib
  
LEMMA Lem_isPrimeType == 
  ASSUME NEW x \in Nat,
         NEW p \in PCR1!VarP,
         NEW i \in Nat
  PROVE PCR1!isPrime(x, p, i) \in BOOLEAN
  OMITTED  

LEMMA Lem_sumType == 
  ASSUME NEW a \in Nat,
         NEW b \in BOOLEAN
  PROVE PCR1!sum(a, b) \in Nat
  BY DEF PCR1!sum

THEOREM Thm_TypeInv == Spec => []TypeInv
<1>1. Init => TypeInv
  <2> SUFFICES ASSUME Init
               PROVE  TypeInv
    OBVIOUS
  <2>1. N \in Nat
    BY DEF Init
  <2>2. map1 \in PCR1!CtxMap
    <3>1. PCR1!initCtx(N) \in PCR1!Ctx 
      BY <2>1 DEF PCR1!initCtx, PCR1!Ctx, PCR1!VarP, PCR1!VarC,
                  PCR1!State
    <3> QED 
      BY <3>1 DEF Init, PCR1!CtxMap
  <2>3. ip1  \in PCR1!IndexMap
    <3>1. PCR1!lowerBnd(N) \in Nat 
      BY DEF PCR1!lowerBnd
    <3> QED 
      BY <3>1 DEF Init, PCR1!IndexMap
  <2> QED
    BY <2>1, <2>2, <2>3 DEF TypeInv
<1>2. TypeInv /\ IteratorType1 /\ IteratorType2 /\ ProducerType /\ [Next]_vars => TypeInv'
  <2>0. SUFFICES ASSUME TypeInv,
                        IteratorType1,
                        IteratorType2,
                        ProducerType,
                        [Next]_vars
                 PROVE  TypeInv'
    OBVIOUS
  <2>1. CASE \E I \in Seq(Nat) : Next1(I)
    <3>0. SUFFICES ASSUME NEW I \in Seq(Nat),
                          Next1(I)
                   PROVE  TypeInv'
      BY <2>1 DEF Next1
    <3>1. N' \in Nat                BY <2>0, <3>0 DEF TypeInv, Next1     
    <3>2. map1 \in PCR1!CtxMap      BY <2>0 DEF TypeInv
    <3>3. map1[I] # Undef           BY <3>0 DEF Next1
    <3>4. map1[I] \in PCR1!Ctx      BY <3>2, <3>3 DEF PCR1!CtxMap 
    <3>5. ip1 \in PCR1!IndexMap     BY <2>0 DEF TypeInv   
    <3>A. CASE /\ PCR1!state(I) = "OFF"
               /\ PCR1!Start(I)
               /\ UNCHANGED ip1  
      <4>1. map1' \in PCR1!CtxMap                                    
        <5>1. map1' = [map1 EXCEPT ![I].ste = "RUN"] BY <3>A DEF PCR1!Start
        <5>2. map1[I].ste' \in PCR1!State BY <3>4, <5>1 DEF PCR1!State, PCR1!Ctx     
        <5>3. map1[I]' \in PCR1!Ctx BY <3>3, <3>4, <5>1, <5>2 DEF PCR1!Ctx
        <5> QED 
          BY <3>2, <5>1, <5>3 DEF PCR1!Ctx, PCR1!CtxMap
      <4>2. ip1' \in PCR1!IndexMap 
        BY <3>5, <3>A     
      <4> QED 
        BY <3>1, <4>1, <4>2 DEF TypeInv        
    <3>B. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!P(I)   
      <4>1. map1' \in PCR1!CtxMap 
        <5>1. /\ ip1[I] \in PCR1!iterator(I)
              /\ map1' = [map1 EXCEPT 
                   ![I].v_p[ip1[I]] = [v |-> PCR1!fib(PCR1!in(I), PCR1!v_p(I), ip1[I]), 
                                       r |-> 0] ]
              /\ ip1' = [ip1 EXCEPT ![I] = ip1[I] + 1]  
          BY <3>B DEF PCR1!P, PCR1!bound, PCR1!i_p, PCR1!step
        <5>2. ip1[I] \in Nat 
          BY <2>0, <3>3, <5>1 DEF PCR1!CtxIndex, IteratorType2   
        <5>3. map1[I].v_p' \in PCR1!VarP
          <6> DEFINE i == ip1[I]
          <6>1. map1[I].v_p' = [map1[I].v_p EXCEPT 
                  ![i] = [v |-> PCR1!fib(PCR1!in(I), PCR1!v_p(I), i), 
                          r |-> 0]] 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>2. i \in Nat BY <5>2                  
          <6>4. PCR1!fib(PCR1!in(I), PCR1!v_p(I), i) \in Nat
            <7>1. PCR1!in(I)  \in Nat              BY <3>4 DEF PCR1!Ctx, PCR1!in    
            <7>2. PCR1!v_p(I) \in PCR1!VarP        BY <3>4 DEF PCR1!Ctx, PCR1!v_p
            <7>3. i \in Nat                        BY <6>2
            <7>4. i >= 2 => /\ PCR1!v_p(I)[i - 1].v \in Nat
                            /\ PCR1!v_p(I)[i - 2].v \in Nat                    
              <8>0. SUFFICES ASSUME i >= 2 
                             PROVE /\ PCR1!v_p(I)[i - 1].v \in Nat
                                   /\ PCR1!v_p(I)[i - 2].v \in Nat 
                OBVIOUS              
              <8>1. I \in PCR1!CtxIndex            
                BY <3>3 DEF PCR1!CtxIndex
              <8>2. i \in PCR1!iterator(I) BY <5>1
              <8>3. N \in Nat BY <2>0 DEF TypeInv
              <8>4. PCR1!iterator(I) = { n \in Nat : 0 <= n /\ n <= N } 
                BY <2>0, <8>1 DEF IteratorType1, PCR1!lowerBnd, PCR1!upperBnd
              <8>5. N >= 2 BY <8>0, <8>2, <8>3, <8>4
              <8>6. i <= N BY <6>2, <8>3, <8>2, <8>4
              <8>7. i-1 \in PCR1!iterator(I) 
                <9>1. i-1 >= 1  BY <6>2, <8>0
                <9>2. i-1 <  N  BY <6>2, <8>3, <8>6
                <9>3. i-1 \in { n \in Nat : 0 <= n /\ n <= N } BY <6>2, <8>3, <9>1, <9>2
                <9> QED  
                  BY <8>4, <9>3
              <8>8. i-2 \in PCR1!iterator(I)
                <9>1. i-2 >= 0  BY <6>2, <8>0
                <9>2. i-2 <  N  BY <6>2, <8>3, <8>6
                <9>3. i-2 \in { n \in Nat : 0 <= n /\ n <= N } BY <6>2, <8>3, <9>1, <9>2
                <9> QED  
                  BY <8>4, <9>3
              <8>9. PCR1!v_p(I)[i-1] \in [v : Nat, r : Nat] 
                BY <2>0, <5>1, <6>2, <8>1, <8>7 DEF ProducerType, PCR1!i_p 
              <8>10. PCR1!v_p(I)[i-2] \in [v : Nat, r : Nat] 
                BY <2>0, <5>1, <6>2, <8>1, <8>8 DEF ProducerType, PCR1!i_p  
              <8> QED 
                BY <8>9, <8>10   
            <7> QED
              BY <7>1, <7>2, <7>3, <7>4, Lem_fibType           
          <6> QED
            BY <3>4, <6>1, <6>2, <6>4 DEF PCR1!Ctx, PCR1!VarP  
        <5>4. map1[I]' \in PCR1!Ctx 
          BY <3>2, <3>3, <5>1, <5>3 DEF PCR1!CtxMap, PCR1!Ctx
        <5> QED 
          BY <3>2, <5>1, <5>4 DEF PCR1!Ctx, PCR1!CtxMap  
      <4>2. ip1' \in PCR1!IndexMap  
        <5>1. /\ ip1[I] \in PCR1!iterator(I)
              /\ map1' = [map1 EXCEPT 
                   ![I].v_p[ip1[I]] = [v |-> PCR1!fib(PCR1!in(I), PCR1!v_p(I), ip1[I]), 
                                       r |-> 0] ]
              /\ ip1' = [ip1 EXCEPT ![I] = ip1[I] + 1]  
          BY <3>B DEF PCR1!P, PCR1!bound, PCR1!i_p, PCR1!step
        <5>2. ip1' = [ip1 EXCEPT ![I] = ip1[I] + 1]
          BY <5>1
        <5>3. ip1[I] \in Nat 
          BY <2>0, <3>3, <5>1 DEF PCR1!CtxIndex, IteratorType2   
        <5>4. ip1[I]' \in Nat
          <6>1. ip1[I]' = ip1[I] + 1 
            BY <3>5, <5>1 DEF PCR1!IndexMap
          <6> QED 
            BY <5>3, <6>1            
        <5> QED  
          BY <3>5, <5>2, <5>4 DEF PCR1!IndexMap             
      <4> QED 
        BY <3>1, <4>1, <4>2  DEF TypeInv               
    <3>C. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!C(I)
               /\ UNCHANGED ip1    
      <4>1. map1' \in PCR1!CtxMap 
        <5>1. PICK i \in PCR1!iterator(I) :
                /\ PCR1!written(PCR1!v_p(I), i)
                /\ map1' = [map1 EXCEPT 
                     ![I].v_p[i].r = 1, 
                     ![I].v_c[i]   = [v |-> PCR1!isPrime(PCR1!in(I), PCR1!v_p(I), i), 
                                      r |-> 0]]
          BY <3>C DEF PCR1!C
        <5>2. i \in Nat  
          BY <2>0, <3>3 DEF PCR1!CtxIndex, IteratorType2
        <5>3. map1[I].v_p' \in PCR1!VarP 
          <6>1. map1[I].v_p' = [map1[I].v_p EXCEPT ![i] = [map1[I].v_p[i] EXCEPT !.r = 1]] 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>2. map1[I].v_p[i] # Undef 
            BY <5>1 DEF PCR1!written, PCR1!v_p          
          <6>3. map1[I].v_p[i].r' = 1 
            BY <3>4, <5>2, <6>1 DEF PCR1!Ctx, PCR1!VarP
          <6>4. map1[I].v_p[i].r' \in Nat 
            BY <6>3
          <6> QED 
            BY <3>3, <3>4, <5>2, <6>1, <6>2, <6>4 DEF PCR1!Ctx, PCR1!VarP       
        <5>4. map1[I].v_c' \in PCR1!VarC
          <6>1. map1[I].v_c' = [map1[I].v_c EXCEPT 
                  ![i] = [v |-> PCR1!isPrime(PCR1!in(I), PCR1!v_p(I), i), 
                          r |-> 0]] 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>2. map1[I].v_c[i]' = [v |-> PCR1!isPrime(PCR1!in(I), PCR1!v_p(I), i), 
                                   r |-> 0] 
            BY <3>4, <5>2, <6>1 DEF PCR1!Ctx, PCR1!VarC
          <6>3. PCR1!isPrime(PCR1!in(I), PCR1!v_p(I), i) \in BOOLEAN 
            <7>1. PCR1!in(I)  \in Nat        BY <3>4 DEF PCR1!Ctx, PCR1!in    
            <7>2. PCR1!v_p(I) \in PCR1!VarP  BY <3>4 DEF PCR1!Ctx, PCR1!v_p
            <7>3. i \in Nat                  BY <5>2
            <7> QED
              BY <7>1, <7>2, <7>3, Lem_isPrimeType          
          <6> QED
             BY <3>4, <5>2, <6>1, <6>3 DEF PCR1!Ctx, PCR1!VarC             
        <5>5. map1[I]' \in PCR1!Ctx
          BY <3>2, <3>3, <5>1, <5>3, <5>4 DEF PCR1!CtxMap, PCR1!Ctx      
        <5> QED 
          BY <3>2, <5>1, <5>5 DEF PCR1!Ctx, PCR1!CtxMap       
      <4>2. ip1' \in PCR1!IndexMap 
        BY <3>5, <3>C      
      <4> QED 
        BY <3>1, <4>1, <4>2 DEF TypeInv                  
    <3>D. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!R(I) 
               /\ UNCHANGED ip1    
      <4>1. map1' \in PCR1!CtxMap 
        <5>1. PICK i \in PCR1!iterator(I) : 
                /\ PCR1!written(PCR1!v_c(I), i)
                /\ map1' = [map1 EXCEPT 
                     ![I].ret      = PCR1!sum(map1[I].ret, PCR1!v_c(I)[i].v),
                     ![I].v_c[i].r = map1[I].v_c[i].r + 1,
                     ![I].ste      = IF PCR1!cDone(I, i) THEN "END" ELSE map1[I].ste]
          BY <3>D DEF PCR1!R
        <5>2. i \in Nat  
          BY <2>0, <3>3 DEF PCR1!CtxIndex, IteratorType2
        <5>3. map1[I].v_c[i] # Undef 
            BY <5>1 DEF PCR1!written, PCR1!v_c      
        <5>4. map1[I].ret' \in Nat
          <6>1. map1[I].ret' = PCR1!sum(map1[I].ret, PCR1!v_c(I)[i].v) 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>2. PCR1!sum(map1[I].ret, PCR1!v_c(I)[i].v) \in Nat 
            <7>1. map1[I].ret      \in Nat        BY <3>4 DEF PCR1!Ctx  
            <7>2. PCR1!v_c(I)      \in PCR1!VarC  BY <3>4 DEF PCR1!Ctx, PCR1!v_c      
            <7>3. PCR1!v_c(I)[i].v \in BOOLEAN    BY <7>2, <5>2, <5>3 DEF PCR1!VarC, PCR1!v_c
            <7> QED
              BY <7>1, <7>3, Lem_sumType          
          <6> QED BY <6>1, <6>2
        <5>5. map1[I].v_c' \in PCR1!VarC
          <6>1. map1[I].v_c' = [map1[I].v_c EXCEPT 
                                  ![i] = [map1[I].v_c[i] EXCEPT 
                                            !.r = map1[I].v_c[i].r + 1]] 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx               
          <6>2. map1[I].v_c[i].r' = map1[I].v_c[i].r + 1  
            BY <3>4, <5>2, <6>1 DEF PCR1!Ctx, PCR1!VarC        
          <6>3. map1[I].v_c[i].r \in Nat 
            BY <3>4, <5>2, <5>3 DEF PCR1!CtxMap, PCR1!Ctx, PCR1!VarC
          <6>4. map1[I].v_c[i].r' \in Nat 
            BY <6>2, <6>3
          <6> QED
            BY <3>4, <5>2, <5>3, <6>1, <6>4 DEF PCR1!Ctx, PCR1!VarC
        <5>6. map1[I].ste' \in PCR1!State
          <6>1. map1[I].ste' = IF PCR1!cDone(I, i) THEN "END" ELSE map1[I].ste 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>A. CASE PCR1!cDone(I, i) 
            <7>1. map1[I].ste' = "END" BY <6>1, <6>A
            <7>2. "END" \in PCR1!State BY DEF PCR1!State           
            <7> QED BY <7>1, <7>2
          <6>B. CASE ~ PCR1!cDone(I, i) 
            <7>1. map1[I].ste' = map1[I].ste BY <6>1, <6>B
            <7>2. map1[I].ste \in PCR1!State BY <3>4 DEF PCR1!CtxMap, PCR1!Ctx         
            <7> QED BY <7>1, <7>2          
          <6> QED 
            BY <6>A, <6>B
        <5>7. map1[I]' \in PCR1!Ctx
          BY <3>2, <3>3, <5>1, <5>4, <5>5, <5>6 DEF PCR1!CtxMap, PCR1!Ctx
        <5> QED 
          BY <3>2, <3>3, <3>4, <5>1, <5>7 DEF PCR1!Ctx, PCR1!CtxMap
      <4>2. ip1' \in PCR1!IndexMap 
        BY <3>5, <3>D    
      <4> QED 
        BY <3>1, <4>1, <4>2 DEF TypeInv                      
    <3>E. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!Eureka(I) 
               /\ UNCHANGED ip1    
      <4>1. map1' \in PCR1!CtxMap 
        <5>1. map1' = [map1 EXCEPT ![I].ste = "END"] BY <3>E DEF PCR1!Eureka
        <5>2. map1[I].ste' \in PCR1!State BY <3>4, <5>1 DEF PCR1!State, PCR1!Ctx     
        <5>3. map1[I]' \in PCR1!Ctx BY <3>3, <3>4, <5>1, <5>2 DEF PCR1!Ctx
        <5> QED 
          BY <3>2, <5>1, <5>3 DEF PCR1!Ctx, PCR1!CtxMap
      <4>2. ip1' \in PCR1!IndexMap   
        BY <3>5, <3>E        
      <4> QED 
        BY <3>1, <4>1, <4>2 DEF TypeInv           
    <3>F. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!Quit(I) 
               /\ UNCHANGED ip1    
      <4>1. map1' \in PCR1!CtxMap                                    
        <5>1. map1' = [map1 EXCEPT ![I].ste = "END"] BY <3>F DEF PCR1!Quit
        <5>2. map1[I].ste' \in PCR1!State BY <3>4, <5>1 DEF PCR1!State, PCR1!Ctx     
        <5>3. map1[I]' \in PCR1!Ctx BY <3>3, <3>4, <5>1, <5>2 DEF PCR1!Ctx
        <5> QED 
          BY <3>2, <5>1, <5>3 DEF PCR1!Ctx, PCR1!CtxMap
      <4>2. ip1' \in PCR1!IndexMap 
        BY <3>5, <3>F 
      <4> QED 
        BY <3>1, <4>1, <4>2 DEF TypeInv                                                              
    <3> QED
      BY <3>0, <3>A, <3>B, <3>C, <3>D, <3>E, <3>F DEF Next1, PCR1!Next
  <2>2. CASE Done
    <3>1. /\ N'    \in Nat
          /\ map1' \in PCR1!CtxMap  
          /\ ip1'  \in PCR1!IndexMap  BY <2>0, <2>2 DEF Done, TypeInv, vars
    <3> QED 
      BY <3>1 DEF TypeInv
  <2>3. CASE UNCHANGED vars
    <3>1. /\ N'    \in Nat
          /\ map1' \in PCR1!CtxMap  
          /\ ip1'  \in PCR1!IndexMap  BY <2>0, <2>3 DEF TypeInv, vars  
    <3> QED 
      BY <3>1 DEF TypeInv
  <2> QED
    BY <2>0, <2>1, <2>2, <2>3 DEF Next
<1> QED 
  BY <1>1, <1>2, PTL, Lem_IteratorType1, Lem_IteratorType2, Lem_ProducerType DEF Spec    

THEOREM Thm_Correctness == 
  \A n \in InType1 : /\ N = n 
                     /\ Spec 
                     => [](PCR1!finished(<< >>) => PCR1!out(<< >>) = Solution(n))
  PROOF OMITTED 

THEOREM Thm_Termination == 
  \A n \in InType1 : /\ N = n 
                     /\ FairSpec 
                     => Termination
  PROOF OMITTED 

=============================================================================
\* Modification History
\* Last modified Fri Oct 23 15:10:43 UYT 2020 by josedu
\* Created Tue Sep 08 23:52:38 UYT 2020 by josedu
