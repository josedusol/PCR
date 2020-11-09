---------------------- MODULE PCRFibPrimes2GThms_proof ----------------------

CONSTANT Undef

VARIABLES N, cm1, cm2, im1

INSTANCE TLAPS
INSTANCE PCRFibPrimes2GMain

PCRIsPrime        == INSTANCE PCRIsPrimeGThms
PCRFibPrimes1Thms == INSTANCE PCRFibPrimes1GThms

USE DEF IndexType1, IndexType2, CtxIdType1, CtxIdType2 

LEMMA Lem_fibType == \A x, p, i : PCR1!fib(x, p, i) \in VarPType1
  BY DEF PCR1!fib, VarPType1

\*LEMMA Lem_sumType == \A a \in VarRType1, b \in VarCType1 : PCR1!sum(a, b) \in VarRType1
\*  BY DEF PCR1!sum, VarRType1, VarCType1
   
LEMMA Lem_divisorsType == \A x, p, i : PCR2!divisors(x, p, i) \in VarPType2
  BY PCRIsPrime!Lem_BasicFunType DEF VarPType2, PCRIsPrime!PCR1!divisors,
       PCRIsPrime!VarPType1

LEMMA Lem_notDividesType == \A x, p, i : PCR2!notDivides(x, p, i) \in VarCType2
  BY PCRIsPrime!Lem_BasicFunType DEF VarCType2, PCR2!notDivides, PCRIsPrime!PCR1!notDivides

LEMMA Lem_andType == \A a, b : PCR2!and(a, b) \in VarRType2
  BY PCRIsPrime!Lem_BasicFunType DEF VarRType2, PCR2!and, PCRIsPrime!PCR1!and

LEMMA Lem_BasicFunType == 
  /\ \A x, p, i : PCR1!fib(x, p, i)        \in VarPType1
  /\ \A a, b :    PCR1!sum(a, b)           \in VarRType1
  /\ \A x, p, i : PCR2!divisors(x, p, i)   \in VarPType2
  /\ \A x, p, i : PCR2!notDivides(x, p, i) \in VarCType2
  /\ \A a, b    : PCR2!and(a, b)           \in VarRType2
  BY Lem_fibType, Lem_divisorsType, Lem_notDividesType, Lem_andType

LEMMA Lem_IteratorType == Spec => []IteratorType
 
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
                  PCR1!State, VarRType1
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
<1>2. TypeInv /\ IteratorType /\ [Next]_vars => TypeInv'
  <2>0. SUFFICES ASSUME TypeInv,
                        IteratorType,
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
          BY <2>0, <3>3, <5>1 DEF PCR1!CtxIndex, IteratorType   
        <5>3. cm1[I].v_p' \in PCR1!VarP
          <6> DEFINE i == im1[I]
          <6>1. cm1[I].v_p' = [cm1[I].v_p EXCEPT 
                  ![i] = [v |-> PCR1!fib(PCR1!in(I), PCR1!v_p(I), i), 
                          r |-> 0]] 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>2. i \in Nat BY <5>2                  
          <6> HIDE DEF i
          <6>4. PCR1!fib(PCR1!in(I), PCR1!v_p(I), i) \in VarPType1 
            BY Lem_BasicFunType DEF VarPType1           
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
          BY <2>0, <3>3, <5>1 DEF PCR1!CtxIndex, IteratorType   
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
                /\ PCR1!isPrime!wellDef(I \o <<i>>)
                /\ cm1' = [cm1 EXCEPT 
                     ![I].v_c[i] = [v |-> PCR1!isPrime!out(I \o <<i>>), 
                                    r |-> 0]]
          BY <3>D DEF PCR1!C_ret
        <5>2. i \in Nat  
          BY <2>0, <3>3 DEF PCR1!CtxIndex, IteratorType 
        <5>3. cm1[I].v_c' \in PCR1!VarC
          <6>1. cm1[I].v_c' = [cm1[I].v_c EXCEPT 
                                 ![i] = [v |-> PCR1!isPrime!out(I \o <<i>>), 
                                         r |-> 0]] 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>2. cm1[I].v_c[i]' = [v |-> PCR1!isPrime!out(I \o <<i>>), 
                                  r |-> 0] 
            BY <3>4, <5>2, <6>1 DEF PCR1!Ctx, PCR1!VarC
          <6>3. PCR1!isPrime!out(I \o <<i>>) \in VarCType1 
            <7>1. I \o <<i>> \in Seq(Nat) BY <5>2
            <7>2. cm2[I \o <<i>>] # Undef 
              BY <5>1 DEF PCR1!isPrime!wellDef 
            <7>3. cm2[I \o <<i>>] \in PCR2!Ctx        
              BY <3>6, <7>1, <7>2 DEF PCR2!CtxMap, PCR2!Ctx        
            <7> QED 
              BY <7>3 DEF PCR1!isPrime!out, PCR2!Ctx, VarRType2, VarCType1
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
          BY <2>0, <3>3 DEF PCR1!CtxIndex, IteratorType    
        <5>3. cm1[I].ret' \in VarRType1
          <6>1. cm1[I].ret' = PCR1!sum(cm1[I].ret, PCR1!v_c(I)[i].v) 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx, PCR1!out
          <6>2. PCR1!sum(cm1[I].ret, PCR1!v_c(I)[i].v) \in VarRType1 
            BY Lem_BasicFunType 
          <6> QED BY <6>1, <6>2
        <5>4. cm1[I].v_c' \in PCR1!VarC
          <6>1. cm1[I].v_c' = [cm1[I].v_c EXCEPT 
                                  ![i] = [cm1[I].v_c[i] EXCEPT 
                                            !.r = cm1[I].v_c[i].r + 1]] 
            BY <3>2, <5>1 DEF PCR1!CtxMap, PCR1!Ctx
          <6>2. cm1[I].v_c[i] # Undef 
            BY <5>1 DEF PCR1!written, PCR1!v_c          
          <6>3. cm1[I].v_c[i].r' = cm1[I].v_c[i].r + 1  
            BY <3>4, <5>2, <6>1 DEF PCR1!Ctx, PCR1!VarC        
          <6>4. cm1[I].v_c[i].r \in Nat 
            BY <3>4, <5>2, <6>2 DEF PCR1!CtxMap, PCR1!Ctx, PCR1!VarC
          <6>5. cm1[I].v_c[i].r' \in Nat 
            BY <6>3, <6>4
          <6> QED
            BY <3>2, <3>4, <5>2, <6>1, <6>2, <6>5 DEF PCR1!CtxMap, PCR1!Ctx, PCR1!VarC
        <5>5. cm1[I].ste' \in PCR1!State
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
        <5>6. cm1[I]' \in PCR1!Ctx
          BY <3>2, <3>3, <3>4, <5>1, <5>3, <5>4, <5>5 DEF PCR1!CtxMap, PCR1!Ctx
        <5> QED 
          BY <3>2, <3>3, <5>1, <5>6 DEF PCR1!Ctx, PCR1!CtxMap      
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
    <3>2. cm1' \in PCR1!CtxMap     BY <2>0, <3>0 DEF Next2, TypeInv  
    <3>3. im1'  \in PCR1!IndexMap   BY <2>0, <3>0 DEF Next2, TypeInv    
    <3>4. cm2  \in PCR2!CtxMap     BY <2>0 DEF TypeInv
    <3>5. cm2[I] # Undef           BY <3>0 DEF Next2
    <3>6. cm2[I] \in PCR2!Ctx      BY <3>4, <3>5 DEF PCR2!CtxMap        
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
        BY <2>0, <3>5 DEF PCR2!CtxIndex, IteratorType   
      <4>3. cm2[I].v_p' \in PCR2!VarP
        <5>1. cm2[I].v_p' = [cm2[I].v_p EXCEPT 
                                ![i] = [v |-> PCR2!divisors(PCR2!in(I), PCR2!v_p(I), i), 
                                        r |-> 0]] 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx                          
        <5>2. PCR2!divisors(PCR2!in(I), PCR2!v_p(I), i) \in VarPType2
          BY Lem_BasicFunType
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
                   ![I].v_p[i].r = 1, 
                   ![I].v_c[i]   = [v |-> PCR2!notDivides(PCR2!in(I), PCR2!v_p(I), i), 
                                    r |-> 0]]
        BY <3>C DEF PCR2!C
      <4>2. i \in Nat  
        BY <2>0, <3>5 DEF PCR2!CtxIndex, IteratorType
      <4>3. cm2[I].v_p' \in PCR2!VarP 
        <5>1. cm2[I].v_p' = [cm2[I].v_p EXCEPT 
                                ![i] = [cm2[I].v_p[i] EXCEPT !.r = 1]] 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx
        <5>2. cm2[I].v_p[i] # Undef 
          BY <4>1 DEF PCR2!written, PCR2!v_p          
        <5>3. cm2[I].v_p[i].r' = 1 
          BY <3>6, <4>2, <5>1 DEF PCR2!Ctx, PCR2!VarP
        <5>4. cm2[I].v_p[i].r' \in Nat 
          BY <5>3
        <5> QED 
          BY <3>6, <4>2, <5>1, <5>2, <5>4 DEF PCR2!Ctx, PCR2!VarP        
      <4>4. cm2[I].v_c' \in PCR2!VarC
        <5>1. cm2[I].v_c' = [cm2[I].v_c EXCEPT 
                                ![i] = [v |-> PCR2!notDivides(PCR2!in(I), PCR2!v_p(I), i), 
                                        r |-> 0]] 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx
        <5>2. cm2[I].v_c[i]' = [v |-> PCR2!notDivides(PCR2!in(I), PCR2!v_p(I), i), 
                                 r |-> 0] 
          BY <3>6, <4>2, <5>1 DEF PCR2!Ctx, PCR2!VarC
        <5>3. PCR2!notDivides(PCR2!in(I), PCR2!v_p(I), i) \in VarCType2 
          BY Lem_BasicFunType
        <5> QED
           BY <3>6, <4>2, <5>1, <5>3 DEF PCR2!Ctx, PCR2!VarC             
      <4>5. cm2[I]' \in PCR2!Ctx
        BY <3>4, <3>5, <3>6, <4>1, <4>3, <4>4 DEF PCR2!CtxMap, PCR2!Ctx      
      <4>6. cm2' \in PCR2!CtxMap
        BY <3>4, <4>1, <4>5 DEF PCR2!Ctx, PCR2!CtxMap                      
      <4> QED 
        BY <3>1, <3>2, <3>3, <4>6 DEF TypeInv                      
    <3>D. CASE /\ PCR2!state(I) = "RUN"
               /\ PCR2!R(I) 
      <4>1. PICK i \in PCR2!iterator(I) : 
              /\ PCR2!written(PCR2!v_c(I), i)
              /\ cm2' = [cm2 EXCEPT 
                   ![I].ret      = PCR2!and(cm2[I].ret, PCR2!v_c(I)[i].v),
                   ![I].v_c[i].r = cm2[I].v_c[i].r + 1,
                   ![I].ste      = IF PCR2!cDone(I, i) THEN "END" ELSE cm2[I].ste]
        BY <3>D DEF PCR2!R
      <4>2. i \in Nat  
        BY <2>0, <3>5 DEF PCR2!CtxIndex, IteratorType    
      <4>3. cm2[I].ret' \in VarRType2       
        <5>1. cm2[I].ret' = PCR2!and(cm2[I].ret, PCR2!v_c(I)[i].v) 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx
        <5>2. PCR2!and(cm2[I].ret, PCR2!v_c(I)[i].v) \in VarRType2 
          BY Lem_BasicFunType
        <5> QED 
          BY <5>1, <5>2
      <4>4. cm2[I].v_c' \in PCR2!VarC    
        <5>1. cm2[I].v_c' = [cm2[I].v_c EXCEPT 
                                ![i] = [cm2[I].v_c[i] EXCEPT 
                                          !.r = cm2[I].v_c[i].r + 1]] 
          BY <3>4, <4>1 DEF PCR2!CtxMap, PCR2!Ctx  
        <5>2. cm2[I].v_c[i] # Undef 
          BY <4>1 DEF PCR2!written, PCR2!v_c                
        <5>3. cm2[I].v_c[i].r' = cm2[I].v_c[i].r + 1  
          BY <3>6, <4>2, <5>1 DEF PCR2!Ctx, PCR2!VarC        
        <5>4. cm2[I].v_c[i].r \in Nat 
          BY <3>6, <4>2, <5>2 DEF PCR2!CtxMap, PCR2!Ctx, PCR2!VarC
        <5>5. cm2[I].v_c[i].r' \in Nat 
          BY <5>3, <5>4
        <5> QED
          BY <3>4, <3>6, <4>2, <5>1, <5>2, <5>5 DEF PCR2!CtxMap, PCR2!Ctx, PCR2!VarC
      <4>5. cm2[I].ste' \in PCR2!State 
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
      <4>6. cm2[I]' \in PCR2!Ctx
        BY <3>4, <3>5, <3>6, <4>1, <4>3, <4>4, <4>5 DEF PCR2!CtxMap, PCR2!Ctx
      <4>7. cm2' \in PCR2!CtxMap 
        BY <3>4, <4>1, <4>6 DEF PCR2!CtxMap, PCR2!Ctx
      <4> QED 
        BY <3>1, <3>2, <3>3, <4>7 DEF TypeInv                                                     
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
  BY <1>1, <1>2, PTL, Lem_IteratorType DEF Spec    

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
\* Last modified Fri Nov 06 20:54:55 UYT 2020 by josedu
\* Created Wed Sep 09 00:33:06 UYT 2020 by josedu
