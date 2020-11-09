------------------------- MODULE PCRFibPrimes2GThms -------------------------

CONSTANT Undef

VARIABLES N, cm1, cm2, im1

INSTANCE TLAPS
INSTANCE PCRFibPrimes2GMain

PCRIsPrimeThms    == INSTANCE PCRIsPrimeGThms
PCRFibPrimes1Thms == INSTANCE PCRFibPrimes1GThms

USE DEF IndexType1, CtxIdType1, InType1, VarPType1, VarCType1, VarRType1,
        IndexType2, CtxIdType2, InType2, VarPType2, VarCType2, VarRType2
       
LEMMA Lem_IteratorType1 == Spec => []IteratorType1
  OMITTED

LEMMA Lem_IteratorType2 == Spec => []IteratorType2
  OMITTED

LEMMA Lem_ProducerType == Spec => []ProducerType
  OMITTED
 
THEOREM Thm_TypeInv == Spec => []TypeInv
<1>1. Init => TypeInv
  <2> SUFFICES ASSUME Init
               PROVE  TypeInv
    OBVIOUS
  <2>1. N    \in InType1
    BY DEF Init
  <2>2. cm1 \in PCR1!CtxMap
    <3>1. PCR1!initCtx(N) \in PCR1!Ctx 
      BY <2>1 DEF PCR1!initCtx, PCR1!Ctx, PCR1!VarP, PCR1!VarC,
                  PCR1!State
    <3> QED 
      BY <3>1 DEF Init, PCR1!CtxMap  
  <2>3. cm2 \in PCR2!CtxMap
    BY DEF Init, PCR2!CtxMap  
  <2>4. im1  \in PCR1!IndexMap
    <3>1. PCR1!lowerBnd(N) \in Nat 
      BY DEF PCR1!lowerBnd
    <3> QED 
      BY <3>1 DEF Init, PCR1!IndexMap  
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4 DEF TypeInv
<1>2. /\ TypeInv 
      /\ IteratorType1 
      /\ IteratorType2 
      /\ ProducerType 
      /\ [Next]_vars 
      => TypeInv'
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
    <3>1. N' \in InType1                 BY <2>0, <3>0 DEF TypeInv, Next1
    <3>2. cm1 \in PCR1!CtxMap            BY <2>0 DEF TypeInv
    <3>3. cm1[I] # Undef                 BY <3>0 DEF Next1
    <3>4. cm1[I] \in PCR1!Ctx            BY <3>2, <3>3 DEF PCR1!CtxMap 
    <3>5. im1 \in PCR1!IndexMap          BY <2>0 DEF TypeInv  
    <3>6. cm2 \in PCR2!CtxMap            BY <2>0 DEF TypeInv            
    <3>A. CASE /\ PCR1!state(I) = "OFF"
               /\ PCR1!Start(I)
               /\ UNCHANGED <<cm2,im1>>   
      <4>1. cm2' \in PCR2!CtxMap     BY <2>0, <3>A DEF TypeInv
      <4>2. im1'  \in PCR1!IndexMap   BY <2>0, <3>A DEF TypeInv
      <4>3. cm1' \in PCR1!CtxMap 
        <5>1. cm1' = [cm1 EXCEPT ![I].ste = "RUN"] BY <3>A DEF PCR1!Start
        <5>2. cm1[I].ste' \in PCR1!State BY <3>4, <5>1 DEF PCR1!State, PCR1!Ctx     
        <5>3. cm1[I]' \in PCR1!Ctx BY <3>3, <3>4, <5>1, <5>2 DEF PCR1!Ctx
        <5> QED 
          BY <3>2, <5>1, <5>3 DEF PCR1!Ctx, PCR1!CtxMap  
      <4> QED 
        BY <3>1, <4>1, <4>2, <4>3 DEF TypeInv       
    <3>B. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!P(I)   
               /\ UNCHANGED <<cm2>>
      <4>1. cm2' \in PCR2!CtxMap     BY <2>0, <3>B DEF TypeInv 
      <4>2. cm1' \in PCR1!CtxMap
        <5>1. /\ im1[I] \in PCR1!iterator(I)
              /\ cm1' = [cm1 EXCEPT 
                   ![I].v_p[im1[I]] = [v |-> PCR1!fib(PCR1!in(I), PCR1!v_p(I), im1[I]), 
                                       r |-> 0] ]
              /\ im1' = [im1 EXCEPT ![I] = im1[I] + 1]  
          BY <3>B DEF PCR1!P, PCR1!i_p, PCR1!step
        <5>2. im1[I] \in Nat 
          BY <2>0, <3>3, <5>1 DEF PCR1!CtxIndex, IteratorType2   
        <5>3. cm1[I].v_p' \in PCR1!VarP
          <6>0. DEFINE i == im1[I]
          <6>1. cm1[I].v_p' = [cm1[I].v_p EXCEPT 
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
              BY <7>1, <7>2, <7>3, <7>4, PCRFibPrimes1Thms!Lem_fibType DEF PCRFibPrimes1Thms!PCR1!fib,
                                                                           PCR1!fib
          <6> QED
            BY <3>4, <6>1, <6>2, <6>4 DEF PCR1!Ctx, PCR1!VarP  
        <5>4. cm1[I]' \in PCR1!Ctx 
          BY <3>2, <3>3, <3>4, <5>1, <5>3 DEF PCR1!CtxMap, PCR1!Ctx
        <5> QED 
          BY <3>2, <5>1, <5>4 DEF PCR1!Ctx, PCR1!CtxMap          
      <4>3. im1'  \in PCR1!IndexMap 
        <5>1. /\ im1[I] \in PCR1!iterator(I)
              /\ cm1' = [cm1 EXCEPT 
                   ![I].v_p[im1[I]] = [v |-> PCR1!fib(PCR1!in(I), PCR1!v_p(I), im1[I]), 
                                       r |-> 0] ]
              /\ im1' = [im1 EXCEPT ![I] = im1[I] + 1]  
          BY <3>B DEF PCR1!P, PCR1!i_p, PCR1!step
        <5>2. im1' = [im1 EXCEPT ![I] = im1[I] + 1]
          BY <5>1
        <5>3. im1[I] \in Nat 
          BY <2>0, <3>3, <5>1 DEF PCR1!CtxIndex, IteratorType2   
        <5>4. im1[I]' \in Nat
          <6>1. im1[I]' = im1[I] + 1 
            BY <3>5, <5>1 DEF PCR1!IndexMap
          <6> QED 
            BY <5>3, <6>1            
        <5> QED  
          BY <3>5, <5>2, <5>4 DEF PCR1!IndexMap                   
      <4> QED   
        BY <3>1, <4>1, <4>2, <4>3 DEF TypeInv                   
    <3>C. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!C_call(I)
               /\ UNCHANGED im1
      <4>1. im1' \in PCR1!IndexMap   BY <2>0, <3>C DEF TypeInv   
      <4>2. cm1' \in PCR1!CtxMap
      <4>3. cm2' \in PCR2!CtxMap
      <4> QED 
        BY <3>1, <4>1, <4>2, <4>3 DEF TypeInv                    
    <3>D. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!C_ret(I)        
               /\ UNCHANGED <<cm2,im1>> 
      <4>1. cm2' \in PCR2!CtxMap     BY <2>0, <3>D DEF TypeInv  
      <4>2. im1' \in PCR1!IndexMap   BY <2>0, <3>D DEF TypeInv   
      <4>3. cm1' \in PCR1!CtxMap
        <5>1. PICK i \in PCR1!iterator(I) :
                /\ PCR1!written(PCR1!v_p(I), i)
                /\ PCR1!PCRisPrime!wellDef(I \o <<i>>)
                /\ cm1' = [cm1 EXCEPT 
                     ![I].v_c[i] = [v |-> PCR1!PCRisPrime!out(I \o <<i>>), 
                                    r |-> 0]]
          BY <3>D DEF PCR1!C_ret
        <5>2. i \in Nat  
          BY <2>0, <3>3 DEF PCR1!CtxIndex, IteratorType2 
        <5>3. cm1[I].v_c' \in PCR1!VarC
          <6>1. cm1[I].v_c' = [cm1[I].v_c EXCEPT 
                                 ![i] = [v |-> PCR1!PCRisPrime!out(I \o <<i>>), 
                                         r |-> 0]] 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>2. cm1[I].v_c[i]' = [v |-> PCR1!PCRisPrime!out(I \o <<i>>), 
                                  r |-> 0] 
            BY <3>4, <5>2, <6>1 DEF PCR1!Ctx, PCR1!VarC
          <6>3. PCR1!PCRisPrime!out(I \o <<i>>) \in VarCType1 
            <7>1. I \o <<i>> \in Seq(Nat) BY <5>2
            <7>2. cm2[I \o <<i>>] # Undef 
              BY <5>1 DEF PCR1!PCRisPrime!wellDef 
            <7>3. cm2[I \o <<i>>] \in PCR2!Ctx        
              BY <3>6, <7>1, <7>2 DEF PCR2!CtxMap, PCR2!Ctx        
            <7> QED 
              BY <7>3 DEF PCR1!PCRisPrime!out, PCR2!Ctx, VarRType2, VarCType1
          <6> QED
             BY <3>4, <5>2, <6>1, <6>3 DEF PCR1!Ctx, PCR1!VarC             
        <5>4. cm1[I]' \in PCR1!Ctx
          BY <3>2, <3>3, <3>4, <5>1, <5>3 DEF PCR1!CtxMap, PCR1!Ctx      
        <5> QED 
          BY <3>2, <5>1, <5>4 DEF PCR1!Ctx, PCR1!CtxMap      
      <4> QED 
        BY <3>1, <4>1, <4>2, <4>3 DEF TypeInv                               
    <3>E. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!R(I) 
               /\ UNCHANGED <<cm2,im1>>
      <4>1. cm2' \in PCR2!CtxMap     BY <2>0, <3>E DEF Next2, TypeInv  
      <4>2. im1' \in PCR1!IndexMap   BY <2>0, <3>E DEF Next2, TypeInv   
      <4>3. cm1' \in PCR1!CtxMap
        <5> DEFINE newRet(i) == PCR1!sum(PCR1!out(I), PCR1!v_c(I)[i].v)
        <5>        endSte(i) == PCR1!cDone(I, i) \/ PCR1!eCnd(newRet(i))
        <5>1. PICK i \in PCR1!iterator(I) : 
                /\ PCR1!written(PCR1!v_c(I), i)
                /\ cm1' = [cm1 EXCEPT 
                     ![I].ret      = newRet(i),
                     ![I].v_c[i].r = @ + 1,
                     ![I].ste      = IF endSte(i) THEN "END" ELSE @]
          BY <3>E DEF PCR1!R
        <5>2. i \in Nat  
          BY <2>0, <3>3 DEF PCR1!CtxIndex, IteratorType2
        <5>3. cm1[I].v_c[i] # Undef 
            BY <5>1 DEF PCR1!written, PCR1!v_c          
        <5>4. cm1[I].ret' \in Nat
          <6>1. cm1[I].ret' = PCR1!sum(cm1[I].ret, PCR1!v_c(I)[i].v) 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx, PCR1!out
          <6>2. PCR1!sum(cm1[I].ret, PCR1!v_c(I)[i].v) \in Nat 
            <7>1. cm1[I].ret       \in Nat        BY <3>4 DEF PCR1!Ctx  
            <7>2. PCR1!v_c(I)      \in PCR1!VarC  BY <3>4 DEF PCR1!Ctx, PCR1!v_c      
            <7>3. PCR1!v_c(I)[i].v \in BOOLEAN    BY <7>2, <5>2, <5>3 DEF PCR1!VarC, PCR1!v_c
            <7> QED
              BY <7>1, <7>3, PCRFibPrimes1Thms!Lem_sumType DEF PCRFibPrimes1Thms!PCR1!sum,
                                                               PCR1!sum  
          <6> QED BY <6>1, <6>2
        <5>5. cm1[I].v_c' \in PCR1!VarC
          <6>1. cm1[I].v_c' = [cm1[I].v_c EXCEPT 
                                  ![i] = [cm1[I].v_c[i] EXCEPT 
                                            !.r = cm1[I].v_c[i].r + 1]] 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx      
          <6>2. cm1[I].v_c[i].r' = cm1[I].v_c[i].r + 1  
            BY <3>4, <5>2, <6>1 DEF PCR1!Ctx, PCR1!VarC        
          <6>3. cm1[I].v_c[i].r \in Nat 
            BY <3>4, <5>2, <5>3 DEF PCR1!CtxMap, PCR1!Ctx, PCR1!VarC
          <6>4. cm1[I].v_c[i].r' \in Nat 
            BY <6>2, <6>3
          <6> QED
            BY <3>2, <3>4, <5>2, <5>3, <6>1, <6>4 DEF PCR1!CtxMap, PCR1!Ctx, PCR1!VarC
        <5>6. cm1[I].ste' \in PCR1!State
          <6>1. cm1[I].ste' = IF endSte(i) THEN "END" ELSE cm1[I].ste 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>A. CASE PCR1!cDone(I, i) 
            <7>1. cm1[I].ste' = "END" BY <6>1, <6>A
            <7>2. "END" \in PCR1!State BY DEF PCR1!State           
            <7> QED BY <7>1, <7>2
          <6>B. CASE ~ PCR1!cDone(I, i) 
            <7>1. cm1[I].ste' = cm1[I].ste BY <6>1, <6>B DEF PCR1!eCnd
            <7>2. cm1[I].ste \in PCR1!State BY <3>4 DEF PCR1!CtxMap, PCR1!Ctx         
            <7> QED BY <7>1, <7>2          
          <6> QED 
            BY <6>A, <6>B
        <5>7. cm1[I]' \in PCR1!Ctx
          BY <3>2, <3>3, <3>4, <5>1, <5>4, <5>5, <5>6 DEF PCR1!CtxMap, PCR1!Ctx
        <5> QED 
          BY <3>2, <3>3, <3>4, <5>1, <5>7 DEF PCR1!Ctx, PCR1!CtxMap      
      <4> QED 
        BY <3>1, <4>1, <4>2, <4>3 DEF TypeInv                                             
    <3>F. CASE /\ PCR1!state(I) = "RUN"
               /\ PCR1!Quit(I) 
               /\ UNCHANGED <<cm2,im1>>
      <4>1. cm2' \in PCR2!CtxMap     BY <2>0, <3>F DEF TypeInv  
      <4>2. im1' \in PCR1!IndexMap   BY <2>0, <3>F DEF TypeInv   
      <4>3. cm1' \in PCR1!CtxMap  
        <5>1. cm1' = [cm1 EXCEPT ![I].ste = "END"] 
          BY <3>F DEF PCR1!Quit
        <5>2. cm1[I].ste' \in PCR1!State 
          BY <3>4, <5>1 DEF PCR1!State, PCR1!Ctx     
        <5>3. cm1[I]' \in PCR1!Ctx 
          BY <3>3, <3>4, <5>1, <5>2 DEF PCR1!Ctx
        <5> QED 
          BY <3>2, <5>1, <5>3 DEF PCR1!Ctx, PCR1!CtxMap 
      <4> QED   
        BY <3>1, <4>1, <4>2, <4>3 DEF TypeInv                                        
    <3> QED
      BY <3>0, <3>A, <3>B, <3>C, <3>D, <3>E, <3>F DEF Next1, PCR1!Next, PCR1!C
  <2>2. CASE \E I \in Seq(Nat) : Next2(I)
    <3>0. SUFFICES ASSUME NEW I \in Seq(Nat),
                          Next2(I)
                   PROVE  TypeInv'
      BY <2>2 DEF Next2
    <3>1. N'    \in InType1         BY <2>0, <3>0 DEF Next2, TypeInv
    <3>2. cm1'  \in PCR1!CtxMap     BY <2>0, <3>0 DEF Next2, TypeInv  
    <3>3. im1'  \in PCR1!IndexMap   BY <2>0, <3>0 DEF Next2, TypeInv    
    <3>4. cm2   \in PCR2!CtxMap     BY <2>0 DEF TypeInv
    <3>5. cm2[I] # Undef            BY <3>0 DEF Next2
    <3>6. cm2[I] \in PCR2!Ctx       BY <3>4, <3>5 DEF PCR2!CtxMap        
    <3>A. CASE /\ PCR2!state(I) = "OFF"
               /\ PCR2!Start(I) 
      <4>1. cm2' = [cm2 EXCEPT ![I].ste = "RUN"] BY <3>A DEF PCR2!Start
      <4>2. cm2[I].ste' \in PCR2!State BY <3>6, <4>1 DEF PCR2!State, PCR2!Ctx     
      <4>3. cm2[I]' \in PCR2!Ctx BY <3>5, <3>6, <4>1, <4>2 DEF PCR2!Ctx  
      <4>4. cm2' \in PCR2!CtxMap BY <3>4, <4>1, <4>3 DEF PCR2!Ctx, PCR2!CtxMap  
      <4> QED 
        BY <3>1, <3>2, <3>3, <4>4 DEF TypeInv      
    <3>B. CASE /\ PCR2!state(I) = "RUN"
               /\ PCR2!P(I)          
      <4>1. PICK i \in PCR2!iterator(I) :
              cm2' = [cm2 EXCEPT 
                ![I].v_p[i] = [v |-> PCR2!divisors(PCR2!in(I), PCR2!v_p(I), i), 
                               r |-> 0] ]
        BY <3>B DEF PCR2!P
      <4>2. i \in Nat 
        BY <2>0, <3>5 DEF PCR2!CtxIndex, IteratorType2   
      <4>3. cm2[I].v_p' \in PCR2!VarP
        <5>1. cm2[I].v_p' = [cm2[I].v_p EXCEPT 
                                ![i] = [v |-> PCR2!divisors(PCR2!in(I), PCR2!v_p(I), i), 
                                        r |-> 0]] 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx                          
        <5>2. PCR2!divisors(PCR2!in(I), PCR2!v_p(I), i) \in Nat
          <6>1. PCR2!in(I)  \in Nat              BY <3>6 DEF PCR2!Ctx, PCR2!in    
          <6>2. PCR2!v_p(I) \in PCR2!VarP        BY <3>6 DEF PCR2!Ctx, PCR2!v_p   
          <6>3. i \in Nat                        BY <4>2          
          <6> QED 
            BY <6>1, <6>2, <6>3, PCRIsPrimeThms!Lem_divisorsType DEF PCRIsPrimeThms!PCR1!divisors,
                                                                     PCR2!divisors   
        <5> QED
          BY <3>6, <4>2, <5>1, <5>2 DEF PCR2!Ctx, PCR2!VarP  
      <4>4. cm2[I]' \in PCR2!Ctx 
        BY <3>4, <3>5, <3>6, <4>1, <4>3 DEF PCR2!CtxMap, PCR2!Ctx
      <4>5. cm2' \in PCR2!CtxMap   
        BY <3>4, <4>1, <4>4 DEF PCR2!Ctx, PCR2!CtxMap         
      <4> QED 
        BY <3>1, <3>2, <3>3, <4>5 DEF TypeInv                           
    <3>C. CASE /\ PCR2!state(I) = "RUN"
               /\ PCR2!C(I)                                  
      <4>1. PICK i \in PCR2!iterator(I) :
              /\ PCR2!written(PCR2!v_p(I), i)
              /\ cm2' = [cm2 EXCEPT
                   ![I].v_p[i].r = @ + 1, 
                   ![I].v_c[i]   = [v |-> PCR2!notDivides(PCR2!in(I), PCR2!v_p(I), i), 
                                    r |-> 0]]
        BY <3>C DEF PCR2!C
      <4>2. i \in Nat  
        BY <2>0, <3>5 DEF PCR2!CtxIndex, IteratorType2
      <4>3. cm2[I].v_p[i] # Undef 
        BY <4>1 DEF PCR2!written, PCR2!v_p               
      <4>4. cm2[I].v_p' \in PCR2!VarP 
        <5>1. cm2[I].v_p' = [cm2[I].v_p EXCEPT 
                                ![i] = [cm2[I].v_p[i] EXCEPT !.r = cm2[I].v_p[i].r + 1]] 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx     
        <5>2. cm2[I].v_p[i].r' = cm2[I].v_p[i].r + 1 
          BY <3>6, <4>2, <5>1 DEF PCR2!Ctx, PCR2!VarP
        <5>3. cm2[I].v_p[i].r \in Nat 
          BY <3>6, <4>2, <4>3 DEF PCR2!Ctx, PCR2!VarP  
        <5>4. cm2[I].v_p[i].r' \in Nat 
          BY <5>2, <5>3
        <5>5. cm2[I].v_p[i].v' \in Nat 
          BY <3>6, <4>2, <4>3, <5>1 DEF PCR2!Ctx, PCR2!VarP         
        <5> QED 
          BY <3>6, <4>2, <4>3, <5>1, <5>4, <5>5 DEF PCR2!Ctx, PCR2!VarP        
      <4>5. cm2[I].v_c' \in PCR2!VarC
        <5>1. cm2[I].v_c' = [cm2[I].v_c EXCEPT 
                                ![i] = [v |-> PCR2!notDivides(PCR2!in(I), PCR2!v_p(I), i), 
                                        r |-> 0]] 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx
        <5>2. cm2[I].v_c[i]' = [v |-> PCR2!notDivides(PCR2!in(I), PCR2!v_p(I), i), 
                                r |-> 0] 
          BY <3>6, <4>2, <5>1 DEF PCR2!Ctx, PCR2!VarC
        <5>3. PCR2!notDivides(PCR2!in(I), PCR2!v_p(I), i) \in BOOLEAN 
          <6>1. PCR2!in(I)  \in Nat              BY <3>6 DEF PCR2!Ctx, PCR2!in    
          <6>2. PCR2!v_p(I) \in PCR2!VarP        BY <3>6 DEF PCR2!Ctx, PCR2!v_p   
          <6>3. i \in Nat                        BY <4>2    
          <6>4. PCR2!v_p(I)[i].v \in Nat         BY <3>6, <4>2, <4>3 DEF PCR2!Ctx, PCR2!VarP, PCR2!v_p 
          <6> QED 
            BY <6>1, <6>2, <6>3, <6>4, PCRIsPrimeThms!Lem_notDividesType DEF PCRIsPrimeThms!PCR1!notDivides,
                                                                             PCR2!notDivides
        <5> QED
           BY <3>6, <4>2, <5>1, <5>3 DEF PCR2!Ctx, PCR2!VarC             
      <4>6. cm2[I]' \in PCR2!Ctx
        BY <3>4, <3>5, <3>6, <4>1, <4>4, <4>5 DEF PCR2!CtxMap, PCR2!Ctx      
      <4>7. cm2' \in PCR2!CtxMap
        BY <3>4, <4>1, <4>6 DEF PCR2!Ctx, PCR2!CtxMap                      
      <4> QED 
        BY <3>1, <3>2, <3>3, <4>7 DEF TypeInv                      
    <3>D. CASE /\ PCR2!state(I) = "RUN"
               /\ PCR2!R(I) 
      <4> DEFINE newRet(i) == PCR2!and(PCR2!out(I), PCR2!v_c(I)[i].v)
      <4>        endSte(i) == PCR2!cDone(I, i) \/ PCR2!eCnd(newRet(i))         
      <4>1. PICK i \in PCR2!iterator(I) : 
              /\ PCR2!written(PCR2!v_c(I), i)
              /\ cm2' = [cm2 EXCEPT 
                   ![I].ret      = newRet(i),
                   ![I].v_c[i].r = @ + 1,
                   ![I].ste      = IF endSte(i) THEN "END" ELSE @]
        BY <3>D DEF PCR2!R
      <4>2. i \in Nat  
        BY <2>0, <3>5 DEF PCR2!CtxIndex, IteratorType2 
      <4>3. cm2[I].v_c[i] # Undef 
        BY <4>1 DEF PCR2!written, PCR2!v_c     
      <4>4. cm2[I].ret' \in BOOLEAN       
        <5>1. cm2[I].ret' = PCR2!and(cm2[I].ret, PCR2!v_c(I)[i].v) 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx
        <5>2. PCR2!and(cm2[I].ret, PCR2!v_c(I)[i].v) \in BOOLEAN 
          <6>1. cm2[I].ret       \in BOOLEAN    BY <3>6 DEF PCR2!Ctx  
          <6>2. PCR2!v_c(I)      \in PCR2!VarC  BY <3>6 DEF PCR2!Ctx, PCR2!v_c      
          <6>3. PCR2!v_c(I)[i].v \in BOOLEAN    BY <6>2, <4>2, <4>3 DEF PCR2!VarC, PCR2!v_c        
          <6> QED 
            BY <6>1, <6>3, PCRIsPrimeThms!Lem_andType DEF PCRIsPrimeThms!PCR1!and, PCR2!and 
        <5> QED 
          BY <5>1, <5>2
      <4>5. cm2[I].v_c' \in PCR2!VarC    
        <5>1. cm2[I].v_c' = [cm2[I].v_c EXCEPT 
                                ![i] = [cm2[I].v_c[i] EXCEPT 
                                          !.r = cm2[I].v_c[i].r + 1]] 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx            
        <5>2. cm2[I].v_c[i].r' = cm2[I].v_c[i].r + 1  
          BY <3>6, <4>2, <5>1 DEF PCR2!Ctx, PCR2!VarC        
        <5>3. cm2[I].v_c[i].r \in Nat 
          BY <3>6, <4>2, <4>3 DEF PCR2!Ctx, PCR2!VarC
        <5>4. cm2[I].v_c[i].r' \in Nat 
          BY <5>2, <5>3
        <5>5. cm2[I].v_c[i].v' \in BOOLEAN 
          BY <3>6, <4>2, <4>3, <5>1 DEF PCR2!Ctx, PCR2!VarC   
        <5> QED
          BY <3>6, <4>2, <4>3, <5>1, <5>4, <5>5 DEF PCR2!Ctx, PCR2!VarC
      <4>6. cm2[I].ste' \in PCR2!State 
        <5>1. cm2[I].ste' = IF PCR2!cDone(I, i) THEN "END" ELSE cm2[I].ste 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx
        <5>A. CASE PCR2!cDone(I, i) 
          <6>1. cm2[I].ste' = "END" BY <5>1, <5>A
          <6>2. "END" \in PCR2!State BY DEF PCR2!State           
          <6> QED BY <6>1, <6>2
        <5>B. CASE ~ PCR2!cDone(I, i) 
          <6>1. cm2[I].ste' = cm2[I].ste BY <5>1, <5>B
          <6>2. cm2[I].ste \in PCR2!State BY <3>6 DEF PCR2!CtxMap, PCR2!Ctx         
          <6> QED BY <6>1, <6>2          
        <5> QED 
          BY <5>A, <5>B               
      <4>7. cm2[I]' \in PCR2!Ctx
        BY <3>4, <3>5, <3>6, <4>1, <4>4, <4>5, <4>6 DEF PCR2!CtxMap, PCR2!Ctx
      <4>8. cm2' \in PCR2!CtxMap 
        BY <3>4, <3>5, <3>6, <4>1, <4>7 DEF PCR2!CtxMap, PCR2!Ctx
      <4> QED 
        BY <3>1, <3>2, <3>3, <4>8 DEF TypeInv                                                     
    <3>E. CASE /\ PCR2!state(I) = "RUN"
               /\ PCR2!Quit(I)                                        
      <4>1. cm2' = [cm2 EXCEPT ![I].ste = "END"] BY <3>E DEF PCR2!Quit
      <4>2. cm2[I].ste' \in PCR2!State BY <3>6, <4>1 DEF PCR2!State, PCR2!Ctx     
      <4>3. cm2[I]' \in PCR2!Ctx BY <3>5, <3>6, <4>1, <4>2 DEF PCR2!Ctx
      <4>4. cm2' \in PCR2!CtxMap BY <3>4, <4>1, <4>3 DEF PCR2!Ctx, PCR2!CtxMap                 
      <4> QED 
        BY <3>1, <3>2, <3>3, <4>4 DEF TypeInv                                                                           
    <3> QED
      BY <3>0, <3>A, <3>B, <3>C, <3>D, <3>E DEF Next2, PCR2!Next  
  <2>3. CASE Done
    <3>1. /\ N'   \in InType1
          /\ cm1' \in PCR1!CtxMap  
          /\ cm2' \in PCR2!CtxMap  
          /\ im1' \in PCR1!IndexMap  BY <2>0, <2>3 DEF Done, TypeInv, vars
    <3> QED 
      BY <3>1 DEF TypeInv  
  <2>4. CASE UNCHANGED vars
    <3>1. /\ N'    \in InType1
          /\ cm1' \in PCR1!CtxMap  
          /\ cm2' \in PCR2!CtxMap  
          /\ im1'  \in PCR1!IndexMap  BY <2>0, <2>4 DEF TypeInv, vars  
    <3> QED 
      BY <3>1 DEF TypeInv
  <2> QED
    BY <2>0, <2>1, <2>2, <2>3, <2>4 DEF Next
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

THEOREM Thm_Refinement == Spec => PCRFibPrimes1!Spec
  PROOF OMITTED

=============================================================================
\* Modification History
\* Last modified Sat Nov 07 19:38:58 UYT 2020 by josedu
\* Created Wed Sep 09 00:33:06 UYT 2020 by josedu
