-------------------------- MODULE PCR_A_c_B ---------------------------------

(*
  PCR composed through consumer with a basic PCR.
   
  `.-----------------------------------------------------------------
    // PCR A
         
    fun fp1(x1,p1,i) = ...                 // fp1 : T x St(Tp1) x N -> Tp1  
    fun fr1(x1,c1,i) = ...                 // fr1 : T x St(D2) x N -> D1  

    dep p1(i-k) -> p1(i)
    dep p1(i[+/-]k) -> c1(i)
    dep c1(i[+/-]k) -> r1(i)
    
    lbnd A = \x1. ...
    ubnd A = \x1. ...
    prop A = \i. ...    
   
    PCR A(x1)                              // x1 \in T
      par
        p1 = produce fp1 x1 p1
        c1 = consume B x1 p1
        r1 = reduce Op1 id1 (fr1 x1 c1)    // r1 \in D1  

    // PCR B
                                           // T2 = T x St(Tp1) x N
    fun fp2(x2,p2,j) = ...                 // fp2 : T2 x St(Tp2) x N -> Tp2
    fun fc2(x2,p2,j) = ...                 // fc2 : T2 x St(Tp2) x N -> Tc2
    fun fr2(x2,c2,j) = ...                 // fr2 : T2 x St(Tc2) x N -> D2

    dep p2(i-k) -> p2(i)
    dep p2(i[+/-]k) -> c2(i)
    dep c2(i[+/-]k) -> r2(i)

    lbnd B = \x2. ...
    ubnd B = \x2. ...
    prop B = \j. ...
        
    PCR B(x2)                              // x2 \in T2
      par
        p2 = produce fp1 x2 p2
        c2 = consume fc2 x2 p2
        r2 = reduce Op2 id2 (fr2 x2 c2)    // r2 \in D2  
  -----------------------------------------------------------------.'  
*)

EXTENDS AbstractAlgebra, Naturals, Sequences, Bags, SeqUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  PCR A constants and variables
*)

CONSTANTS I0, pre(_),             
          T, Tp1, D1, 
          id1, Op1(_,_),
          lBnd1(_), uBnd1(_), prop1(_),
          fp1(_,_,_), fr1(_,_,_), gp1(_,_),
          Dep_pp1, Dep_pc1, Dep_cr1

VARIABLES in, X1, p1, c1, r1, rs1

(* 
  PCR B constants and variables
*)

CONSTANTS Tp2, Tc2, D2,
          id2, Op2(_,_),
          lBnd2(_), uBnd2(_), prop2(_),        
          fp2(_,_,_), fc2(_,_,_), fr2(_,_,_), gp2(_,_),  
          Dep_pp2, Dep_pc2, Dep_cr2 

VARIABLES X2, p2, c2, r2, rs2         
              
----------------------------------------------------------------------------

(* 
  General definitions
*)

Undef == CHOOSE x : x \notin UNION {T, Tp1, Tp2, Tc2, D1, D2}

wrt(v)       == v # Undef
wrts(v,S)    == \A k \in S : wrt(v[k])
eqs(v1,v2,S) == \A k \in S : wrt(v1[k]) /\ v1[k] = v2[k]

----------------------------------------------------------------------------

(* 
  PCR A definitions and assumptions
*)

IndexA    == Seq(Nat)
AssigA    == Nat
ItA(x)    == {i \in lBnd1(x)..uBnd1(x) : prop1(i)}
WDIndexA  == {I \in IndexA : wrt(X1[I])}
StA(R)    == [AssigA -> R \union {Undef}] 
redA(I,i) == rs1[I][i]
endA(I)   == \A i \in ItA(X1[I]) : redA(I,i)

depsA(x,d,i) == 
         {i-k : k \in {k \in d[1] : i-k >= lBnd1(x) /\ prop1(i-k)}} 
  \union {i} 
  \union {i+k : k \in {k \in d[2] : i+k <= uBnd1(x) /\ prop1(i+k)}} 

AXIOM H_TypeA ==
  /\ I0   \in IndexA
  /\ \A x \in T   : lBnd1(x) \in Nat
  /\ \A x \in T   : uBnd1(x) \in Nat
  /\ \A i \in Nat : prop1(i) \in BOOLEAN
  /\ \A x \in T   : pre(x) \in BOOLEAN
  /\ Dep_pp1 \in (SUBSET (Nat\{0})) \X (SUBSET {})
  /\ Dep_pc1 \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))
  /\ Dep_cr1 \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))   

AXIOM H_BFunTypeA ==
  \A x \in T, i \in AssigA :
    /\ gp1(x,i) \in Tp1 \union {Undef}
    /\ \A vp \in StA(Tp1) : fp1(x,vp,i) \in Tp1 \union {Undef}
    /\ \A vc \in StA(D2)  : fr1(x,vc,i) \in D1  \union {Undef}

AXIOM H_BFunWDA ==
  \A x \in T : \A i \in ItA(x) : 
    /\ gp1(x,i) \in Tp1
    /\ \A vp \in StA(Tp1) : wrts(vp,depsA(x,Dep_pp1,i)\{i}) => fp1(x,vp,i) \in Tp1
    /\ \A vc \in StA(D2)  : wrts(vc,depsA(x,Dep_cr1,i))     => fr1(x,vc,i) \in D1  

AXIOM H_fpRelevanceA == 
  \A x \in T : \A i \in ItA(x), vp1 \in StA(Tp1), vp2 \in StA(Tp1) :
    eqs(vp1,vp2,depsA(x,Dep_pp1,i)\{i}) => fp1(x,vp1,i) = fp1(x,vp2,i)    

AXIOM H_frRelevanceA == 
  \A x \in T : \A i \in ItA(x), vc1 \in StA(D2), vc2 \in StA(D2) :
    eqs(vc1,vc2,depsA(x,Dep_cr1,i)) => fr1(x,vc1,i) = fr1(x,vc2,i) 

LEMMA H_ProdEqInvA ==
  \A x \in T : \A i \in ItA(x) :
    wrt(p1[I0][i]) => fp1(x,p1[I0],i) = gp1(x,i)

(* 
  PCR B definitions and assumptions
*)

IndexB    == Seq(Nat)
AssigB    == Nat
ItB(x)    == {i \in lBnd2(x)..uBnd2(x) : prop2(i)}
WDIndexB  == {I \in IndexB : wrt(X2[I])}
StB(R)    == [AssigB -> R \union {Undef}] 
redB(I,i) == rs2[I][i]
endB(I)   == \A i \in ItB(X2[I]) : redB(I,i)

depsB(x,d,i) == 
         {i-k : k \in {k \in d[1] : i-k >= lBnd2(x) /\ prop2(i-k)}} 
  \union {i} 
  \union {i+k : k \in {k \in d[2] : i+k <= uBnd2(x) /\ prop2(i+k)}} 

T2 == T \X StA(Tp1) \X AssigA

AXIOM H_TypeB ==
  /\ \A x \in T2  : lBnd2(x) \in Nat
  /\ \A x \in T2  : uBnd2(x) \in Nat
  /\ \A i \in Nat : prop2(i) \in BOOLEAN
  /\ Dep_pp2 \in (SUBSET (Nat\{0})) \X (SUBSET {})
  /\ Dep_pc2 \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))
  /\ Dep_cr2 \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))   

AXIOM H_BFunTypeB ==
  \A x \in T2, i \in AssigB :
    /\ gp2(x,i) \in Tp2 \union {Undef}
    /\ \A vp \in StB(Tp2) : fp2(x,vp,i) \in Tp2 \union {Undef}
    /\ \A vp \in StB(Tp2) : fc2(x,vp,i) \in Tc2 \union {Undef}
    /\ \A vc \in StB(Tc2) : fr2(x,vc,i) \in D2  \union {Undef}

AXIOM H_BFunWDB ==
  \A x \in T2 : \A i \in ItB(x) : 
    /\ gp2(x,i) \in Tp2
    /\ \A vp \in StB(Tp2) : wrts(vp,depsB(x,Dep_pp2,i)\{i}) => fp2(x,vp,i) \in Tp2
    /\ \A vp \in StB(Tp2) : wrts(vp,depsB(x,Dep_pc2,i))     => fc2(x,vp,i) \in Tc2
    /\ \A vc \in StB(Tc2) : wrts(vc,depsB(x,Dep_cr2,i))     => fr2(x,vc,i) \in D2  

AXIOM H_fpRelevanceB == 
  \A x \in T2 : \A i \in ItB(x), vp1 \in StB(Tp2), vp2 \in StB(Tp2) : 
    eqs(vp1,vp2,depsB(x,Dep_pp2,i)\{i}) => fp2(x,vp1,i) = fp2(x,vp2,i)
      
AXIOM H_fcRelevanceB == 
  \A x \in T2 : \A i \in ItB(x), vp1 \in StB(Tp2), vp2 \in StB(Tp2) :
    eqs(vp1,vp2,depsB(x,Dep_pc2,i)) => fc2(x,vp1,i) = fc2(x,vp2,i)      

AXIOM H_frRelevanceB == 
  \A x \in T2 : \A i \in ItB(x), vc1 \in StB(Tc2), vc2 \in StB(Tc2) :  
    eqs(vc1,vc2,depsB(x,Dep_cr2,i)) => fr2(x,vc1,i) = fr2(x,vc2,i)

LEMMA H_ProdEqInvB ==
  \A I \in WDIndexB : \A i \in ItB(X2[I]) :
    wrt(p1[I][i]) => fp2(X2[I],p2[I],i) = gp2(X2[I],i)

----------------------------------------------------------------------------

(* 
  Functional specification
*)

M2 == INSTANCE AbelianMonoidBigOp 
  WITH D <- D2, Id <- id2, \otimes <- Op2  

AXIOM H_AlgebraB == AbelianMonoid(D2, id2, Op2)

Gp2(x)    == [i \in AssigB |-> gp2(x,i)]  
Fc2(x,vc) == [i \in AssigB |-> fc2(x,vc,i)]
Fr2(x,vc) == [i \in AssigB |-> fr2(x,vc,i)]

B(x2) == M2!BigOpP(lBnd2(x2), uBnd2(x2), prop2, 
                   LAMBDA j : Fr2(x2,Fc2(x2,Gp2(x2)))[j])

M1 == INSTANCE AbelianMonoidBigOp 
  WITH D <- D1, Id <- id1, \otimes <- Op1

AXIOM H_AlgebraA == AbelianMonoid(D1, id1, Op1)

Gp1(x)     == [i \in AssigA |-> gp1(x,i)]  
Fc1(x1,vp) == [i \in AssigA |-> B(<<x1,vp,i>>)]
Fr1(x,vc)  == [i \in AssigA |-> fr1(x,vc,i)] 

A(x1) == M1!BigOpP(lBnd1(x1), uBnd1(x1), prop1,
                   LAMBDA i : Fr1(x1,Fc1(x1,Gp1(x1)))[i])

----------------------------------------------------------------------------

(* 
  Operational specification
*)

vs1 == <<X1,p1,c1,r1,rs1,X2>>
vs2 == <<p2,c2,r2,rs2>>

InitA == /\ in \in T /\ pre(in)
         /\ X1  = [I \in IndexA |-> IF I = I0 THEN in ELSE Undef]        
         /\ p1  = [I \in IndexA |-> [i \in AssigA |-> Undef]]
         /\ c1  = [I \in IndexA |-> [i \in AssigA |-> Undef]]   
         /\ rs1 = [I \in IndexA |-> [i \in AssigA |-> FALSE]]
         /\ r1  = [I \in IndexA |-> id1]

InitB == /\ X2  = [I \in IndexB |-> Undef]
         /\ p2  = [I \in IndexB |-> [i \in AssigB |-> Undef]]
         /\ c2  = [I \in IndexB |-> [i \in AssigB |-> Undef]]   
         /\ rs2 = [I \in IndexB |-> [i \in AssigB |-> FALSE]]
         /\ r2  = [I \in IndexB |-> id2]

Init == InitA /\ InitB
        
P1(I,i) == 
  /\ ~ wrt(p1[I][i]) 
  /\ wrts(p1[I], depsA(X1[I],Dep_pp1,i)\{i})
  /\ p1' = [p1 EXCEPT ![I][i] = fp1(X1[I],p1[I],i)]
  /\ UNCHANGED <<X1,c1,r1,rs1,X2>>

C1ini(I,i) == 
  /\ ~ wrt(X2[I \o <<i>>])
  /\ wrts(p1[I], depsA(X1[I],Dep_pc1,i))
  /\ X2' = [X2 EXCEPT ![I \o <<i>>] = <<X1[I],p1[I],i>>]
  /\ UNCHANGED <<X1,p1,c1,r1,rs1>>
             
C1end(I,i) == 
  /\ ~ wrt(c1[I][i]) 
  /\ wrt(X2[I \o <<i>>])
  /\ endB(I \o <<i>>)
  /\ c1' = [c1 EXCEPT ![I][i] = r2[I \o <<i>>]]
  /\ UNCHANGED <<X1,p1,r1,rs1,X2>>

R1(I,i) == 
  /\ ~ redA(I,i)
  /\ wrts(c1[I], depsA(X1[I],Dep_cr1,i))
  /\ r1'  = [r1   EXCEPT ![I]    = Op1(@, fr1(X1[I],c1[I],i))]  
  /\ rs1' = [rs1 EXCEPT ![I][i] = TRUE]
  /\ UNCHANGED <<X1,p1,c1,X2>>      
         
P2(I,i) == 
  /\ ~ wrt(p2[I][i]) 
  /\ wrts(p2[I], depsB(X2[I],Dep_pp2,i)\{i})
  /\ p2' = [p2 EXCEPT ![I][i] = fp2(X2[I],p2[I],i)]
  /\ UNCHANGED <<c2,r2,rs2>>        

C2(I,i) == 
  /\ ~ wrt(c2[I][i]) 
  /\ wrts(p2[I], depsB(X2[I],Dep_pc2,i)) 
  /\ c2' = [c2 EXCEPT ![I][i] = fc2(X2[I],p2[I],i)]
  /\ UNCHANGED <<p2,r2,rs2>>  

R2(I,i) == 
  /\ ~ redB(I,i)
  /\ wrts(c2[I], depsB(X2[I],Dep_cr2,i))
  /\ r2'  = [r2  EXCEPT ![I]    = Op2(@, fr2(X2[I],c2[I],i))]
  /\ rs2' = [rs2 EXCEPT ![I][i] = TRUE]
  /\ UNCHANGED <<p2,c2>>    
 
Done == /\ \A I \in WDIndexA : endA(I) 
        /\ \A I \in WDIndexB : endB(I) 
        /\ UNCHANGED <<in,vs1,vs2>>
        /\ PrintT("Done: In = " \o ToString(X1[I0])
                 \o " - Out = " \o ToString(r1[I0]))              

StepA == /\ \E I \in WDIndexA :
               \E i \in ItA(X1[I]) : \/ P1(I,i)
                                     \/ C1ini(I,i)
                                     \/ C1end(I,i)  
                                     \/ R1(I,i)
         /\ UNCHANGED <<in,vs2>>                           
                              
StepB == /\ \E I \in WDIndexB : 
               \E i \in ItB(X2[I]) : \/ P2(I,i) 
                                     \/ C2(I,i)
                                     \/ R2(I,i)
         /\ UNCHANGED <<in,vs1>> 

Next == StepA \/ StepB \/ Done

Spec == Init /\ [][Next]_<<in,vs1,vs2>>       

FairSpec == Spec /\ WF_vs1(StepA) /\ WF_vs2(StepB)

----------------------------------------------------------------------------

(* 
  PCR A properties
*)                                               

IndexInvA == WDIndexA = { I0 }

TypeInvA == 
  /\ in  \in T
  /\ X1  \in [IndexA -> T \union {Undef}] /\ X1[I0] = in
  /\ p1  \in [IndexA -> StA(Tp1)]
  /\ c1  \in [IndexA -> StA(D2)]
  /\ r1  \in [IndexA -> D1]
  /\ rs1 \in [IndexA -> [AssigA -> BOOLEAN]]
       
PInvA == 
  \A i \in ItA(X1[I0]) : 
    wrt(p1[I0][i]) => /\ wrts(p1[I0],depsA(X1[I0],Dep_pp1,i))
                      /\ p1[I0][i] = gp1(X1[I0],i) 
                      
CInv1A == 
  \A i \in ItA(X1[I0]) : 
    wrt(X2[I0 \o <<i>>]) => /\ wrts(p1[I0],depsA(X1[I0],Dep_pc1,i))
                            /\ \E vp \in StA(Tp1) : 
                                 /\ eqs(vp,p1[I0],depsA(X1[I0],Dep_pc1,i))
                                 /\ X2[I0 \o <<i>>] = <<X1[I0],vp,i>>
CInv2A == 
  \A i \in ItA(X1[I0]) :
    wrt(c1[I0][i]) => /\ wrt(X2[I0 \o <<i>>]) 
                      /\ endB(I0 \o <<i>>)
                      /\ c1[I0][i] = r2[I0 \o <<i>>]  

RInv1A == 
  \A i \in ItA(X1[I0]) : 
    redA(I0,i) => wrts(c1[I0],depsA(X1[I0],Dep_cr1,i))

RInv2A == 
  r1[I0] = M1!BigOpP(lBnd1(X1[I0]), uBnd1(X1[I0]),
                     LAMBDA i : prop1(i) /\ redA(I0,i), 
                     LAMBDA i : fr1(X1[I0],c1[I0],i))

InvA == /\ IndexInvA
        /\ TypeInvA
        /\ PInvA
        /\ CInv1A
        /\ CInv2A
        /\ RInv1A
        /\ RInv2A
        
CorrectnessA == endA(I0) => r1[I0] = A(X1[I0])

TerminationA == <> endA(I0)

GTermination == endA(I0) => \A I \in WDIndexB : endB(I)

(* 
  PCR B properties
*)

IndexInvB == WDIndexB \subseteq {I0 \o <<i>> : i \in AssigA}

TypeInvB == 
  /\ X2  \in [IndexB -> T2 \union {Undef}]
  /\ p2  \in [IndexB -> StB(Tp2)]
  /\ c2  \in [IndexB -> StB(Tc2)]            
  /\ r2  \in [IndexB -> D2]
  /\ rs2 \in [IndexB -> [AssigB -> BOOLEAN]]
                  
PInvB == 
  \A I \in WDIndexB : \A i \in ItB(X2[I]) : 
    wrt(p2[I][i]) => /\ wrts(p2[I],depsB(X2[I],Dep_pp2,i))
                     /\ p2[I][i] = gp2(X2[I],i)

CInvB == 
  \A I \in WDIndexB : \A i \in ItB(X2[I]) : 
    wrt(c2[I][i]) => /\ wrts(p2[I],depsB(X2[I],Dep_pc2,i))
                     /\ c2[I][i] = fc2(X2[I],p2[I],i)
                     
RInv1B == 
  \A I \in WDIndexB : \A i \in ItB(X2[I]) : 
    redB(I,i) => wrts(c2[I],depsB(X2[I],Dep_cr2,i))

RInv2B == 
  \A I \in WDIndexB :
    r2[I] = M2!BigOpP(lBnd2(X2[I]), uBnd2(X2[I]),
                      LAMBDA j : prop2(j) /\ redB(I,j), 
                      LAMBDA j : fr2(X2[I],c2[I],j)) 

InvB == /\ IndexInvB
        /\ TypeInvB
        /\ PInvB
        /\ CInvB
        /\ RInv1B
        /\ RInv2B

CorrectnessB == \A I \in WDIndexB : endB(I) => r2[I] = B(X2[I])
  
TerminationB == <>(\A I \in WDIndexB : endB(I))         

(* 
  Conjoint properties
*)

TypeInv == /\ TypeInvA
           /\ TypeInvB
  
Inv == /\ TypeInv
       /\ InvA
       /\ InvB 
       
Correctness == /\ CorrectnessA
               /\ CorrectnessB

Termination == /\ TerminationA   
               /\ TerminationB

(* 
  Refinement
*)

inS == X1[I0] 
fcS(x1,vp1,i) == B(<<x1,vp1,i>>) 

PCR_A == INSTANCE PCR_A 
  WITH in <- inS, X <- X1, p <- p1, c <- c1, r <- r1, rs <- rs1,
       T <- T, Tp <- Tp1, Tc <- D2, D <- D1, 
       id <- id1, Op <- Op1,
       lBnd <- lBnd1, uBnd <- uBnd1, prop <- prop1,                    
       fp <- fp1, fc <- fcS, fr <- fr1, gp <- gp1,      
       Dep_pp <- Dep_pp1, Dep_pc <- Dep_pc1, Dep_cr <- Dep_cr1

AXIOM H_UndefRestrict == PCR_A!Undef = Undef

AXIOM H_fcSRelevance == 
  \A x \in T : \A i \in ItA(x), vp1 \in StA(Tp1), vp2 \in StA(Tp1) :
    eqs(vp1,vp2,depsA(x,Dep_pc1,i)) => fcS(x,vp1,i) = fcS(x,vp2,i)

=============================================================================
\* Modification History
\* Last modified Thu Sep 09 02:15:58 UYT 2021 by josedu
\* Last modified Wed Jul 07 19:58:23 GMT-03:00 2021 by JosEdu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
