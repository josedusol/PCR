--------------------------- MODULE PCR_A_c_B_Thms ---------------------------

EXTENDS PCR_A_c_B, TLAPS

USE DEF IndexA, IndexB, AssigA, AssigB, redA, redB

M1T == INSTANCE AbelianMonoidBigOpThms
  WITH D <- D1, Id <- id1, \otimes <- Op1 
  
M2T == INSTANCE AbelianMonoidBigOpThms
  WITH D <- D2, Id <- id2, \otimes <- Op2 

LEMMA H_AMon1 == /\ M1T!Monoid(D1, id1, Op1)
                 /\ \A x, y \in D1 : Op1(x, y) = Op1(y, x)
  BY H_AlgebraA DEF AbelianMonoid, M1T!AbelianMonoid,
                    Monoid,        M1T!Monoid, 
                    SemiGroup,     M1T!SemiGroup,
                    Magma,         M1T!Magma

LEMMA H_AMon2 == /\ M2T!Monoid(D2, id2, Op2)
                 /\ \A x, y \in D2 : Op2(x, y) = Op2(y, x)
  BY H_AlgebraB DEF AbelianMonoid, M2T!AbelianMonoid,
                    Monoid,        M2T!Monoid, 
                    SemiGroup,     M2T!SemiGroup,
                    Magma,         M2T!Magma
                   
LEMMA H_M1eqM1T == ASSUME NEW x, NEW y, NEW Q(_), NEW f(_)
                   PROVE /\ M1!BigOp(x,y,f)    = M1T!BigOp(x,y,f)
                         /\ M1!BigOpP(x,y,Q,f) = M1T!BigOpP(x,y,Q,f)
  BY DEF M1!BigOpP, M1T!BigOpP, 
         M1!BigOp,  M1T!BigOp,
         M1!bigOp,  M1T!bigOp 
         
LEMMA H_M2eqM2T == ASSUME NEW x, NEW y, NEW Q(_), NEW f(_)
                   PROVE /\ M2!BigOp(x,y,f)    = M2T!BigOp(x,y,f)
                         /\ M2!BigOpP(x,y,Q,f) = M2T!BigOpP(x,y,Q,f)
  BY DEF M2!BigOpP, M2T!BigOpP, 
         M2!BigOp,  M2T!BigOp,
         M2!bigOp,  M2T!bigOp                          

LEMMA H_Undef == Undef \notin UNION {T, Tp1, Tp2, Tc2, D1, D2} 
  BY NoSetContainsEverything DEF Undef

\* PCR B

THEOREM Thm_IndexInvB == Spec => []IndexInvB

THEOREM Thm_TypeInvA == Spec => []TypeInvA

THEOREM Thm_TypeInvB == Spec => []TypeInvB             
<1>1. Init => TypeInvB
  <2> SUFFICES ASSUME Init
               PROVE  TypeInvB
    OBVIOUS
  <2>1. /\ X2  \in [Seq(Nat) -> T2 \union {Undef}]
        /\ p2  \in [Seq(Nat) -> StB(Tp2)]  
        /\ c2  \in [Seq(Nat) -> StB(Tc2)]
        /\ rs2 \in [Seq(Nat) -> [Nat -> BOOLEAN]]              
    BY DEF Init, StB     
  <2>2. r2 \in [Seq(Nat) -> D2]
    BY H_AlgebraB DEF Init, AbelianMonoid, Monoid          
  <2> QED 
    BY <2>1, <2>2 DEF TypeInvB
<1>2. /\ TypeInvA
      /\ TypeInvB 
      /\ [Next]_<<in,vs1,vs2>> 
      => TypeInvB'
  <2>0. SUFFICES ASSUME TypeInvA,
                        TypeInvB,
                        [Next]_<<in,vs1,vs2>>
                 PROVE  TypeInvB'
    OBVIOUS
  <2>A. CASE StepA
    <3>0. SUFFICES ASSUME \E I \in WDIndexA :
                            \E i \in ItA(X1[I]) : \/ P1(I,i)
                                                  \/ C1ini(I,i)
                                                  \/ C1end(I,i)
                                                  \/ R1(I,i)
                   PROVE TypeInvB'
      BY <2>0, <2>A DEF StepA
    <3>1. PICK I \in WDIndexA :
                 \E i \in ItA(X1[I]) : \/ P1(I,i)
                                       \/ C1ini(I,i)
                                       \/ C1end(I,i)
                                       \/ R1(I,i)
      BY <3>0             
    <3>2. PICK i \in ItA(X1[I]) : \/ P1(I,i)
                                  \/ C1ini(I,i)
                                  \/ C1end(I,i)
                                  \/ R1(I,i)
      BY <3>1  
    <3> DEFINE x1 == X1[I]
               m1 == lBnd1(x1) 
               n1 == uBnd1(x1)              
    <3>3. x1 \in T
      BY <2>0 DEF TypeInvA, WDIndexA, wrt
    <3>4. /\ I \in Seq(Nat)
          /\ i \in Nat
          /\ i \in {k \in m1..n1 : prop1(k)}
          /\ ItA(x1) \subseteq Nat
          /\ I \o <<i>> \in Seq(Nat)
      BY <3>3, H_TypeA DEF WDIndexA, ItA       
    <3>5. vs2' = vs2
      BY <2>A DEF StepA

    <3>A. CASE P1(I,i) 
      BY <2>0, <3>5, <3>A DEF P1, TypeInvB, vs2
    
    <3>B. CASE C1ini(I,i) 
      <4>1. X2' = [X2 EXCEPT ![I \o <<i>>] = <<x1,p1[I],i>>]
        BY <3>B DEF C1ini
      <4>2. X2[I \o <<i>>]' = <<x1,p1[I],i>>
        BY <2>0, <3>4, <4>1 DEF TypeInvB
      <4>3. p1[I] \in StA(Tp1) 
        BY <2>0, <3>4 DEF TypeInvA, StA 
      <4>4. <<x1,p1[I],i>> \in T2
        BY <3>3, <3>4, <4>3 DEF T2
      <4>5. X2' \in [Seq(Nat) -> T2 \union {Undef}]
        BY <2>0, <3>4, <4>1, <4>2, <4>4 DEF TypeInvB
      <4> QED
        BY <2>0, <3>5, <4>5 DEF TypeInvB, vs2
    
    <3>C. CASE C1end(I,i) 
      BY <2>0, <3>5, <3>C DEF C1end, TypeInvB, vs2
    
    <3>D. CASE R1(I,i) 
      BY <2>0, <3>5, <3>D DEF R1, TypeInvB, vs2
    
    <3> QED
      BY <3>2, <3>A, <3>B, <3>C, <3>D
       
  <2>B. CASE StepB
    <3>0. SUFFICES ASSUME \E I \in WDIndexB :
                            \E i \in ItB(X2[I]) : \/ P2(I,i)
                                                  \/ C2(I,i)
                                                  \/ R2(I,i)
                   PROVE TypeInvB'
      BY <2>0, <2>B DEF StepB
    <3>1. PICK I \in WDIndexB :
                 \E i \in ItB(X2[I]) : \/ P2(I,i)
                                       \/ C2(I,i)
                                       \/ R2(I,i)
      BY <3>0             
    <3>2. PICK i \in ItB(X2[I]) : \/ P2(I,i)
                                  \/ C2(I,i)
                                  \/ R2(I,i)
      BY <3>1  
    <3> DEFINE x2 == X2[I]
               m2 == lBnd2(x2) 
               n2 == uBnd2(x2)              
    <3>3. x2 \in T2
      BY <2>0 DEF TypeInvB, WDIndexB, wrt
    <3>4. /\ I \in Seq(Nat)
          /\ i \in Nat
          /\ i \in {k \in m2..n2 : prop2(k)}
          /\ ItB(x2) \subseteq Nat
      BY <3>3, H_TypeB DEF WDIndexB, ItB       
    <3>5. X2' = X2
      BY <2>B DEF StepB, vs1    

    <3>A. CASE P2(I,i) 
      <4>1. /\ X2'  \in [Seq(Nat) -> T2 \union {Undef}]
            /\ c2'  \in [Seq(Nat) -> StB(Tc2)]
            /\ r2'  \in [Seq(Nat) -> D2] 
            /\ rs2' \in [Seq(Nat) -> [Nat -> BOOLEAN]]  
        <5>1. <<X2,c2,r2,rs2>>' = <<X2,c2,r2,rs2>> 
          BY <3>5, <3>A DEF P2
        <5> QED 
          BY <2>0, <5>1 DEF TypeInvB            
      <4>2. p2' \in [Seq(Nat) -> StB(Tp2)]
        <5>1. /\ wrts(p2[I],depsB(x2,Dep_pp2,i)\{i})
              /\ p2' = [p2 EXCEPT ![I][i] = fp2(x2,p2[I],i)]
          BY <3>A DEF P2 
        <5>2. p2 \in [Seq(Nat) -> StB(Tp2)]    
          BY <2>0 DEF TypeInvB 
        <5>3. fp2(x2,p2[I],i) \in Tp2  
          BY <2>0, <3>3, <3>4, <5>1, <5>2, H_BFunWDB
        <5>5. p2[I][i]' \in Tp2 \union {Undef}
          BY <3>4, <5>1, <5>2, <5>3 DEF StB
        <5> QED 
          BY <5>1, <5>2, <5>5 DEF StB      
      <4> QED
        BY <4>1, <4>2 DEF TypeInvB 
                 
    <3>B. CASE C2(I,i)
      <4>1. /\ X2'  \in [Seq(Nat) -> T2 \union {Undef}]
            /\ p2'  \in [Seq(Nat) -> StB(Tp2)]
            /\ r2'  \in [Seq(Nat) -> D2] 
            /\ rs2' \in [Seq(Nat) -> [Nat -> BOOLEAN]]              
        <5>1. <<X2,p2,r2,rs2>>' = <<X2,p2,r2,rs2>> 
          BY <3>5, <3>B DEF C2
        <5> QED 
          BY <2>0, <5>1 DEF TypeInvB          
      <4>2. c2' \in [Seq(Nat) -> StB(Tc2)]
        <5>1. /\ wrts(p2[I],depsB(x2,Dep_pc2,i))
              /\ c2' = [c2 EXCEPT ![I][i] = fc2(x2,p2[I],i)]
          BY <3>B DEF C2 
        <5>2. /\ c2 \in [Seq(Nat) -> StB(Tc2)]   
              /\ p2 \in [Seq(Nat) -> StB(Tp2)]    
          BY <2>0 DEF TypeInvB    
        <5>3. fc2(x2,p2[I],i) \in Tc2
          BY <2>0, <3>3, <3>4, <5>2, <5>1, H_BFunWDB
        <5>5. c2[I][i]' \in Tc2 \union {Undef}
          BY <3>4, <5>1, <5>2, <5>3 DEF StB
        <5> QED 
          BY <5>1, <5>2, <5>5 DEF StB      
      <4> QED
        BY <4>1, <4>2 DEF TypeInvB  
         
    <3>C. CASE R2(I,i) 
      <4>1. /\ X2' \in [Seq(Nat) -> T2 \union {Undef}]
            /\ c2' \in [Seq(Nat) -> StB(Tc2)]
            /\ p2' \in [Seq(Nat) -> StB(Tp2)]
        <5>1. <<X2,p2,c2>>' = <<X2,p2,c2>> 
          BY <3>5, <3>C DEF R2
        <5> QED 
          BY <2>0, <5>1 DEF TypeInvB  
      <4>2. /\ wrts(c2[I],depsB(x2,Dep_cr2,i))
            /\ r2'  = [r2  EXCEPT ![I]    = Op2(@, fr2(x2,c2[I],i))]
            /\ rs2' = [rs2 EXCEPT ![I][i] = TRUE]
        BY <3>C DEF R2     
      <4>3. /\ c2  \in [Seq(Nat) -> StB(Tc2)]
            /\ rs2 \in [Seq(Nat) -> [Nat -> BOOLEAN]] 
            /\ r2  \in [Seq(Nat) -> D2]
        BY <2>0 DEF TypeInvB                 
      <4>4. r2' \in [Seq(Nat) -> D2]  
        <5>1. r2[I] \in D2
          BY <2>0, <3>4 DEF TypeInvB
        <5>2. fr2(x2,c2[I],i) \in D2
          BY <2>0, <3>3, <3>4, <4>2, <4>3, H_BFunWDB    
        <5>3. Op2(r2[I], fr2(x2,c2[I],i)) \in D2
          BY <5>1, <5>2, H_AlgebraB 
          DEF AbelianMonoid, Monoid, SemiGroup, Magma
        <5>6. r2[I]' \in D2
          BY <3>4, <4>2, <4>3, <5>3 DEF StB  
        <5> QED     
          BY <4>2, <4>3, <5>6         
      <4>5. rs2' \in [Seq(Nat) -> [Nat -> BOOLEAN]]
        BY <4>2, <4>3
      <4> QED    
        BY <4>1, <4>4, <4>5 DEF TypeInvB    
        
    <3> QED
      BY <3>2, <3>A, <3>B, <3>C
  <2>C. CASE Done
    <3>1. <<X2,p2,c2,r2,rs2>>' = <<X2,p2,c2,r2,rs2>> 
      BY <2>C DEF Done, vs1, vs2
    <3> QED
      BY <3>1, <2>0 DEF TypeInvB
  <2>D. CASE UNCHANGED <<in,vs1,vs2>>
    <3>1. <<X2,p2,c2,r2,rs2>>' = <<X2,p2,c2,r2,rs2>> 
      BY <2>D DEF vs1, vs2
    <3> QED
      BY <3>1, <2>0 DEF TypeInvB
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C, <2>D DEF Next
<1> QED 
  BY <1>1, <1>2, Thm_TypeInvA, PTL DEF Spec

THEOREM Thm_PInvB == Spec => []PInvB
  
THEOREM Thm_CInvB == Spec => []CInvB

THEOREM Thm_RInv1B == Spec => []RInv1B

THEOREM Thm_RInv2B == Spec => []RInv2B

THEOREM Thm_Inv2 == Spec => []InvB
  BY Thm_IndexInvB, Thm_TypeInvB, Thm_PInvB, Thm_CInvB, 
     Thm_RInv1B, Thm_RInv2B, PTL DEF InvB

THEOREM Thm_CorrectnessB == Spec => []CorrectnessB

\* PCR A

THEOREM Thm_IndexInvA == Spec => []IndexInvA

THEOREM Thm_PInvA == Spec => []PInvA
  
THEOREM Thm_CInv1A == Spec => []CInv1A

THEOREM Thm_CInv2A == Spec => []CInv2A

THEOREM Thm_RInv1A == Spec => []RInv1A

THEOREM Thm_RInv2A == Spec => []RInv2A

THEOREM Thm_Inv1 == Spec => []InvA
  BY Thm_IndexInvA, Thm_TypeInvA, Thm_PInvA, Thm_CInv1A,
     Thm_CInv2A, Thm_RInv1A, Thm_RInv2A, PTL DEF InvA

THEOREM Thm_CorrectnessA == Spec => []CorrectnessA
                   
THEOREM Thm_Refinement == Spec => PCR_A!Spec
<1> DEFINE x1    == X1[I0]
           m1    == lBnd1(x1) 
           n1    == uBnd1(x1)
           Q1(i) == prop1(i)
<1> USE DEF PCR_A!Index, PCR_A!Assig, PCR_A!red                    
<1>1. Init => PCR_A!Init
  <2> SUFFICES ASSUME Init
               PROVE  PCR_A!Init
    OBVIOUS
  <2>1. /\ x1 \in T /\ pre(x1)
        /\ X1  = [I \in Seq(Nat) |-> IF I = I0 THEN x1 ELSE Undef]
        /\ p1  = [I \in Seq(Nat) |-> [i \in Nat |-> Undef]]
        /\ c1  = [I \in Seq(Nat) |-> [i \in Nat |-> Undef]]
        /\ rs1 = [I \in Seq(Nat) |-> [i \in Nat |-> FALSE]]
        /\ r1  = [I \in Seq(Nat) |-> id1]       
    BY H_TypeA DEF Init, InitA       
  <2> QED 
    BY <2>1, H_UndefRestrict DEF PCR_A!Init, inS 
<1>2. /\ InvA
      /\ CorrectnessB 
      /\ [Next]_<<in,vs1,vs2>> 
      => [PCR_A!Next]_<<inS,PCR_A!vs>>
  <2>0. SUFFICES ASSUME IndexInvA, TypeInvA, CInv1A,
                        CorrectnessB,
                        [Next]_<<in,vs1,vs2>>
                 PROVE  [PCR_A!Next]_PCR_A!vs
    BY DEF InvA, inS, PCR_A!vs
  <2>A. CASE StepA
    <3>0. SUFFICES ASSUME \E i \in ItA(x1) : \/ P1(I0,i) 
                                             \/ C1ini(I0,i)
                                             \/ C1end(I0,i)
                                             \/ R1(I0,i)
                   PROVE [PCR_A!Next]_PCR_A!vs
      BY <2>0, <2>A DEF StepA, IndexInvA    
    <3>1. PICK i \in ItA(x1) : \/ P1(I0,i) 
                               \/ C1ini(I0,i)
                               \/ C1end(I0,i)
                               \/ R1(I0,i)
      BY <3>0 
    <3>2. x1 \in T
      BY <2>0 DEF IndexInvA, TypeInvA, WDIndexA, wrt
    <3>3. /\ I0 \in Seq(Nat) 
          /\ I0 \in WDIndexA
          /\ i \in Nat
          /\ i \in {k \in m1..n1 : Q1(k)} 
          /\ ItA(x1) \subseteq Nat
      BY <2>0, <3>2, H_TypeA DEF IndexInvA, WDIndexA, ItA       
    <3>4. m1 \in Nat /\ n1 \in Nat 
      BY <2>0, <3>2, H_TypeA DEF TypeInvA, m1, n1     
    <3>5. /\ I0 \in PCR_A!WDIndex
          /\ i  \in PCR_A!It(x1) 
      BY <3>3, H_UndefRestrict DEF WDIndexA, ItA, wrt, 
         PCR_A!WDIndex, PCR_A!It, PCR_A!wrt

    <3>A. CASE P1(I0,i)    
      <4>0. SUFFICES ASSUME P1(I0,i)
                     PROVE  PCR_A!P(I0,i)
        BY <2>0, <3>5, <3>A DEF P1, inS, PCR_A!Next, PCR_A!Step                   
      <4> QED 
        BY <4>0, H_UndefRestrict DEF P1, wrt, wrts, depsA, 
           PCR_A!P, PCR_A!wrt, PCR_A!wrts, PCR_A!deps
    
    <3>B. CASE C1ini(I0,i)
      <4>0. SUFFICES ASSUME C1ini(I0,i)
                     PROVE  UNCHANGED PCR_A!vs
        BY <2>0, <3>5, <3>B DEF C1ini, PCR_A!Next, PCR_A!Step
      <4>1. UNCHANGED <<X1,p1,c1,r1,rs1>>
        BY <4>0 DEF C1ini      
      <4> QED 
        BY <4>1 DEF PCR_A!vs  
      
    <3>C. CASE C1end(I0,i)
      <4>0. SUFFICES ASSUME C1end(I0,i)
                     PROVE  PCR_A!C(I0,i)
        BY <2>0, <3>5, <3>C DEF C1end, inS, PCR_A!Next, PCR_A!Step
      <4>1. /\ ~ wrt(c1[I0][i]) 
            /\ wrt(X2[I0 \o <<i>>])
            /\ endB(I0 \o <<i>>)
            /\ c1' = [c1 EXCEPT ![I0][i] = r2[I0 \o <<i>>]]
            /\ UNCHANGED <<X1,p1,r1,rs1,X2>>     
        BY <4>0 DEF C1end     
      <4>2. wrts(p1[I0],depsA(x1,Dep_pc1,i))
        BY <2>0, <4>1 DEF CInv1A
      <4>3. PICK vp \in StA(Tp1) :
                   /\ eqs(vp,p1[I0],depsA(x1,Dep_pc1,i))
                   /\ X2[I0 \o <<i>>] = <<x1,vp,i>>
        BY <2>0, <4>1 DEF CInv1A      
      <4>4. p1[I0] \in StA(Tp1)  
        BY <2>0, <3>3 DEF TypeInvA, StA  
      <4>5. I0 \o <<i>> \in WDIndexB 
        BY <3>3, <4>1 DEF WDIndexB  
      
      <4>E1. c1[I0][i]' = r2[I0 \o <<i>>]     BY <2>0, <3>3, <4>1 DEF TypeInvA, StA          
      <4>E2.          @ = B(X2[I0 \o <<i>>])  BY <2>0, <4>1, <4>5 DEF CorrectnessB
      <4>E3.          @ = B(<<x1,vp,i>>)      BY <4>3     
      <4>E4.          @ = fcS(x1,vp,i)        BY DEF fcS
      <4>E5.          @ = fcS(x1,p1[I0],i)    BY <3>2, <4>3, <4>4, H_fcSRelevance 
      
      <4>6. c1[I0][i]' = fcS(x1,p1[I0],i) 
        BY <4>1, <4>E1, <4>E2, <4>E3, <4>E4, <4>E5   
      <4>7. c1' = [c1 EXCEPT ![I0][i] = fcS(x1,p1[I0],i)]    
        BY <4>1, <4>6         
      
      <4>8. /\ ~ wrt(c1[I0][i]) 
            /\ wrts(p1[I0], depsA(x1, Dep_pc1, i))
            /\ c1' = [c1 EXCEPT ![I0][i] = fcS(x1,p1[I0],i)]  
            /\ UNCHANGED <<X1,p1,r1,rs1>>             
        BY <4>1, <4>2, <4>7
      
      <4> QED   
        BY <4>8, H_UndefRestrict DEF PCR_A!C, wrt, wrts, depsA, 
           PCR_A!wrt, PCR_A!wrts, PCR_A!deps   
   
    <3>D. CASE R1(I0,i) 
      <4>0. SUFFICES ASSUME R1(I0,i)
                     PROVE  PCR_A!R(I0,i)
        BY <2>0, <3>5, <3>D DEF R1, inS, PCR_A!Next, PCR_A!Step 
      <4> QED 
        BY <4>0, H_UndefRestrict DEF R1, wrt, wrts, depsA,
           PCR_A!R, PCR_A!wrt, PCR_A!wrts, PCR_A!deps

    <3> QED
      BY <3>1, <3>A, <3>B, <3>C, <3>D

  <2>B. CASE StepB
    <3>0. SUFFICES ASSUME \E I \in WDIndexB : 
                            \E i \in ItB(X2[I]) : \/ P2(I,i) 
                                                  \/ C2(I,i)
                                                  \/ R2(I,i)
                   PROVE UNCHANGED PCR_A!vs
      BY <2>0, <2>B DEF StepB
    <3>1. <<in,vs1>>' = <<in,vs1>>
      BY <2>B DEF StepB   
    <3>2. PCR_A!vs' = PCR_A!vs
      BY <3>1 DEF vs1, PCR_A!vs, wrt       
    <3> QED
      BY <3>2  
  
  <2>C. CASE Done
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs1,vs2>>
                   PROVE  UNCHANGED PCR_A!vs
      BY <2>C DEF Done, vs1, vs2
    <3>1. PCR_A!vs' = PCR_A!vs
      BY <3>0 DEF PCR_A!vs, vs1, vs2, wrt
    <3> QED    
      BY <3>1
  <2>D. CASE UNCHANGED <<in,vs1,vs2>>
    <3>0. SUFFICES ASSUME UNCHANGED <<in,vs1,vs2>> 
                   PROVE  UNCHANGED PCR_A!vs
      BY <2>D DEF vs1, vs2
    <3>1. PCR_A!vs' = PCR_A!vs
      BY <3>0 DEF PCR_A!vs, vs1, vs2, wrt
    <3> QED    
      BY <3>1
  <2> QED
    BY <2>0, <2>A, <2>B, <2>C, <2>D DEF Next
<1> QED 
  BY <1>1, <1>2, Thm_Inv1, Thm_CorrectnessB, PTL DEF Spec, PCR_A!Spec

=============================================================================
\* Modification History
\* Last modified Thu Sep 02 23:30:36 UYT 2021 by josedu
\* Last modified Thu Jul 08 03:49:02 GMT-03:00 2021 by JosEdu
\* Created Sat Jul 03 16:41:28 GMT-03:00 2021 by JosEdu
