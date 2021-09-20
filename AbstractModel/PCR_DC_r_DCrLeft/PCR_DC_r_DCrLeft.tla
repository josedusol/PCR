------------------------- MODULE PCR_DC_r_DCrLeft --------------------------

(*
  Divide-and-conquer PCR composed through reducer with a divide-and-conquer 
  PCR with left reducer.
   
  `.-----------------------------------------------------------------
    // PCR A
    
    fun div1(x1)         = ...                        //    div1 : T -> Seq(T)     
    fun isBase1(x1,p1,i) = ...                        // isBase1 : T x St(T) -> Bool 
    fun base1(x1,p1,i)   = ...                        //   base1 : T x St(T) -> D
    fun fr1(x1,c1,i)     = ...                        //     fr1 : T x St(D) -> D

    fun iterDiv1(x1,p1,i)    = div1(x1)[i]    
    fun subproblem1(x1,p1,i) = if isBase1(x1,p1,i)  
                               then base1(x1,p1,i)
                               else A(p1)    
    fun conquer1(r1,x1,c1,i) = B(r1, fr1(x1,c1,i))

    dep p1(i[+/-]k) -> c1(i)
    dep c1(i[+/-]k) -> r1(i)
   
    lbnd A = \x1. 1 
    ubnd A = \x1. len(div1(x1))
   
    PCR A(x1)                                         // x1 \in T
      par
        p1 = produce iterDiv1 x1
        c1 = consume subproblem1 x1 p1
        r1 = reduce conquer1 id x1 c1                 // r1 \in D
        
    // PCR B
                                                      // T2 = D x D
    fun div2(x2)         = ...                        //    div2 : T2 -> Seq(T2)   
    fun isBase2(x2,p2,i) = ...                        // isBase2 : T2 x St(T2) x N -> Bool 
    fun base2(x2,p2,i)   = ...                        //   base2 : T2 x St(T2) x N -> D
    fun fr2(x2,c2,i)     = ...                        //     fr2 : T2 x St(D) x N -> D

    fun iterDiv2(x2,p2,i)    = div2(x2)[i]     
    fun subproblem2(x2,p2,i) = if isBase2(x2,p2,i)  
                               then base2(x2,p2,i)
                               else B(p2)     
    fun conquer2(r2,x2,c2,i) = Op2(r2, fr2(x2,c2,i)) 

    dep p2(i[+/-]k) -> c2(i)
    dep c2(i[+/-]k) -> r2(i)
    dep r2(i-1) -> r2(i)

    lbnd B = \x2. 1 
    ubnd B = \x2. len(div2(x2))
    
    PCR B(x2)                                         // x2 \in T2
      par
        p2 = produce iterDiv2 x2
        c2 = consume subproblem2 x2 p2
        r2 = reduce conquer2 id x2 c2                 // r2 \in D                
  -----------------------------------------------------------------.'  
*)

EXTENDS AbstractAlgebra, Naturals, Sequences, Bags, SeqUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  PCR A constants and variables 
*)

CONSTANTS I0, pre(_),             
          T, D,
          id,
          div1(_), isBase1(_,_,_), base1(_,_,_), fr1(_,_,_),
          Dep_pc1, Dep_cr1

VARIABLES in, X1, p1, c1, r1, rs1

(* 
  PCR B constants and variables 
*)

CONSTANTS Op2(_,_),
          div2(_), isBase2(_,_,_), base2(_,_,_), fr2(_,_,_),
          Dep_pc2, Dep_cr2

VARIABLES X2, p2, c2, r2, rs2
         
----------------------------------------------------------------------------

(* 
  General definitions
*)

Undef == CHOOSE x : x \notin T \union D

wrt(v)       == v # Undef
wrts(v,S)    == \A k \in S : wrt(v[k])
eqs(v1,v2,S) == \A k \in S : wrt(v1[k]) /\ v1[k] = v2[k]
 
----------------------------------------------------------------------------

(* 
  PCR A definitions and assumptions
*)

IndexA    == Seq(Nat)
AssigA    == Nat
uBnd1(x)  == Len(div1(x))
ItA(x)    == 1..uBnd1(x)
WDIndexA  == {I \in IndexA : wrt(X1[I])}
StA(R)    == [AssigA -> R \union {Undef}] 
redA(I,i) == rs1[I][i]
endA(I)   == \A i \in ItA(X1[I]) : redA(I,i)

depsA(x,d,i) == 
         {i-k : k \in {k \in d[1] : i-k >= 1}} 
  \union {i} 
  \union {i+k : k \in {k \in d[2] : i+k <= uBnd1(x)}} 
  
AXIOM H_TypeA ==
  /\ I0   \in IndexA
  /\ \A x \in T : uBnd1(x) \in Nat
  /\ \A x \in T : pre(x) \in BOOLEAN
  /\ Dep_pc1 \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))
  /\ Dep_cr1 \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))   

AXIOM H_BFunTypeA ==
  \A x \in T, i \in AssigA :
    /\ div1(x) \in Seq(T) \union {Undef}
    /\ \A vp \in StA(T) : isBase1(x,vp,i) \in BOOLEAN \union {Undef}
    /\ \A vp \in StA(T) : base1(x,vp,i)   \in D  \union {Undef}
    /\ \A vc \in StA(D) : fr1(x,vc,i)     \in D  \union {Undef}

AXIOM H_BFunWDA ==
  \A x \in T : \A i \in ItA(x) :
    /\ div1(x) \in Seq(T) 
    /\ \A vp \in StA(T) : wrts(vp,depsA(x,Dep_pc1,i)) => isBase1(x,vp,i) \in BOOLEAN
    /\ \A vp \in StA(T) : wrts(vp,depsA(x,Dep_pc1,i)) => base1(x,vp,i) \in D
    /\ \A vc \in StA(D) : wrts(vc,depsA(x,Dep_cr1,i)) => fr1(x,vc,i) \in D  

AXIOM H_isBaseRelevanceA == 
  \A x \in T : \A i \in ItA(x), vp1 \in StA(T), vp2 \in StA(T) :
    eqs(vp1,vp2,depsA(x,Dep_pc1,i)) => isBase1(x,vp1,i) = isBase1(x,vp2,i)
      
AXIOM H_baseRelevanceA == 
  \A x \in T : \A i \in ItA(x), vp1 \in StA(T), vp2 \in StA(T) :
    eqs(vp1,vp2,depsA(x,Dep_pc1,i)) => base1(x,vp1,i) = base1(x,vp2,i)      

AXIOM H_frRelevanceA == 
  \A x \in T : \A i \in ItA(x), vc1 \in StA(D), vc2 \in StA(D) :
    eqs(vc1,vc2,depsA(x,Dep_cr1,i)) => fr1(x,vc1,i) = fr1(x,vc2,i)

(* 
  PCR B definitions and assumptions
*)

IndexB    == Seq(Nat) \X Seq(Nat)
AssigB    == Nat
uBnd2(x)  == Len(div2(x))
ItB(x)    == 1..uBnd2(x)
WDIndexB  == {I \in IndexB : wrt(X2[I])}
StB(R)    == [AssigB -> R \union {Undef}] 
redB(I,i) == rs2[I][i]
endB(I)   == \A i \in ItB(X2[I]) : redB(I,i)

depsB(x,d,i) == 
         {i-k : k \in {k \in d[1] : i-k >= 1}} 
  \union {i} 
  \union {i+k : k \in {k \in d[2] : i+k <= uBnd2(x)}} 
  
T2 == D \X D

AXIOM H_TypeB ==
  /\ \A x \in T2 : uBnd2(x) \in Nat
  /\ Dep_pc2 \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))
  /\ Dep_cr2 \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))   

AXIOM H_BFunTypeB ==
  \A x \in T2, i \in AssigB :
    /\ div2(x) \in Seq(T2) \union {Undef}
    /\ \A vp \in StB(T2) : isBase2(x,vp,i) \in BOOLEAN \union {Undef}
    /\ \A vp \in StB(T2) : base2(x,vp,i)   \in D  \union {Undef}
    /\ \A vc \in StB(D)  : fr2(x,vc,i)     \in D  \union {Undef}

AXIOM H_BFunWDB ==
  \A x \in T2 : \A i \in ItB(x) :
    /\ div2(x) \in Seq(T2) 
    /\ \A vp \in StB(T2) : wrts(vp,depsB(x,Dep_pc2,i)) => isBase2(x,vp,i) \in BOOLEAN
    /\ \A vp \in StB(T2) : wrts(vp,depsB(x,Dep_pc2,i)) => base2(x,vp,i) \in D
    /\ \A vc \in StB(D)  : wrts(vc,depsB(x,Dep_cr2,i)) => fr2(x,vc,i) \in D  

AXIOM H_isBaseRelevanceB == 
  \A x \in T2 : \A i \in ItB(x), vp1 \in StB(T2), vp2 \in StB(T2) :
    eqs(vp1,vp2,depsB(x,Dep_pc2,i)) => isBase2(x,vp1,i) = isBase2(x,vp2,i)
      
AXIOM H_baseRelevanceB == 
  \A x \in T2 : \A i \in ItB(x), vp1 \in StB(T2), vp2 \in StB(T2) :
    eqs(vp1,vp2,depsB(x,Dep_pc2,i)) => base2(x,vp1,i) = base2(x,vp2,i)      

AXIOM H_frRelevanceB == 
  \A x \in T2 : \A i \in ItB(x), vc1 \in StB(D), vc2 \in StB(D) :
    eqs(vc1,vc2,depsB(x,Dep_cr2,i)) => fr2(x,vc1,i) = fr2(x,vc2,i)

----------------------------------------------------------------------------

(* 
  Functional specification
*)

M2 == INSTANCE MonoidBigOp 
  WITH D <- D, Id <- id, \otimes <- Op2

AXIOM H_AlgebraB == Monoid(D, id, Op2)

Fr2(x,vc) == [i \in AssigB |-> fr2(x,vc,i)]

RECURSIVE B(_)
B(x) == M2!BigOp(1, uBnd2(x), 
                 LAMBDA i : Fr2(x,[k \in AssigB |-> IF isBase2(x,div2(x),k)   
                                                    THEN base2(x,div2(x),k)
                                                    ELSE B(div2(x)[k])])[i])
(* 
  Alternatively, B as a recursive function:

  B[x \in D \X D] == 
    M2!BigOp(1, uBnd2(x), 
             LAMBDA i : Fr2(x,[k \in AssigB |-> IF isBase2(x,div2(x),k)   
                                                THEN base2(x,div2(x),k)
                                                ELSE B[div2(x)[k]]])[i])
*)

Op1(x,y) == B(<<x,y>>)

M1 == INSTANCE AbelianMonoidBigOp 
  WITH D <- D, Id <- id, \otimes <- Op1

AXIOM H_AlgebraA == AbelianMonoid(D, id, Op1)

Fr1(x,vc) == [i \in AssigA |-> fr1(x,vc,i)]

RECURSIVE A(_)
A(x) == M1!BigOp(1, uBnd1(x), 
                 LAMBDA i : Fr1(x,[k \in AssigA |-> IF isBase1(x,div1(x),k)   
                                                    THEN base1(x,div1(x),k)
                                                    ELSE A(div1(x)[k])])[i])
(* 
  Alternatively, A as a recursive function:

  A[x \in T] == 
    M1!BigOp(1, uBnd1(x), 
             LAMBDA i : Fr1(x,[k \in AssigA |-> IF isBase1(x,div1(x),k)   
                                                THEN base1(x,div1(x),k)
                                                ELSE A[div1(x)[k]]])[i]) 
*)

----------------------------------------------------------------------------

(* 
  Operational specification
*)

vs1 == <<X1,p1,c1,r1,rs1>>
vs2 == <<p2,c2,r2,rs2>>

InitA == /\ in \in T /\ pre(in)    
         /\ X1  = [I \in IndexA |-> IF I = I0 THEN in ELSE Undef]        
         /\ p1  = [I \in IndexA |-> [i \in AssigA |-> Undef]]
         /\ c1  = [I \in IndexA |-> [i \in AssigA |-> Undef]]   
         /\ rs1 = [I \in IndexA |-> [i \in AssigA |-> FALSE]]
         /\ r1  = [I \in IndexA |-> id]        
         
InitB == /\ X2  = [I \in IndexB |-> Undef]
         /\ p2  = [I \in IndexB |-> [i \in AssigB |-> Undef]]
         /\ c2  = [I \in IndexB |-> [i \in AssigB |-> Undef]]
         /\ rs2 = [I \in IndexB |-> [i \in AssigB |-> FALSE]]
         /\ r2  = [I \in IndexB |-> id]

Init == InitA /\ InitB

P1(I,i) == 
  /\ ~ wrt(p1[I][i]) 
  /\ p1' = [p1 EXCEPT ![I][i] = div1(X1[I])[i]]
  /\ UNCHANGED <<X1,c1,r1,rs1,X2>>

C1base(I,i) ==
  /\ ~ wrt(c1[I][i])  
  /\ wrts(p1[I], depsA(X1[I],Dep_pc1,i))
  /\ isBase1(X1[I],p1[I],i)  
  /\ c1' = [c1 EXCEPT ![I][i] = base1(X1[I],p1[I],i)]
  /\ UNCHANGED <<X1,p1,r1,rs1,X2>> 

C1ini(I,i) == 
  /\ ~ wrt(X1[I \o <<i>>]) 
  /\ wrts(p1[I], depsA(X1[I],Dep_pc1,i))
  /\ ~ isBase1(X1[I],p1[I],i)
  /\ X1' = [X1 EXCEPT ![I \o <<i>>] = p1[I][i]]
  /\ UNCHANGED <<p1,c1,r1,rs1,X2>> 
             
C1end(I,i) == 
  /\ ~ wrt(c1[I][i])
  /\ wrt(X1[I \o <<i>>]) 
  /\ endA(I \o <<i>>)     
  /\ c1' = [c1 EXCEPT ![I][i] = r1[I \o <<i>>]]
  /\ UNCHANGED <<X1,p1,r1,rs1,X2>>           

R1ini(I,i) == 
  /\ ~ wrt(X2[<<I,<<i>>>>])
  /\ wrts(c1[I], depsA(X1[I],Dep_cr1,i))
  /\ ~ \E k \in ItA(X1[I]) : /\ k # i
                             /\ wrt(X2[<<I,<<k>>>>])
                             /\ ~ redA(I,k)              
  /\ X2' = [X2 EXCEPT ![<<I,<<i>>>>] = <<r1[I], fr1(X1[I],c1[I],i)>>]
  /\ UNCHANGED <<X1,p1,c1,r1,rs1>>      

R1end(I,i) == 
  /\ ~ redA(I,i) 
  /\ wrt(X2[<<I,<<i>>>>]) 
  /\ endB(<<I,<<i>>>>)  
  /\ r1'  = [r1  EXCEPT ![I]    = r2[<<I, <<i>>>>]]
  /\ rs1' = [rs1 EXCEPT ![I][i] = TRUE]     
  /\ UNCHANGED <<X1,p1,c1,X2>> 

\* PCR B

P2(I,i) == 
  /\ ~ wrt(p2[I][i]) 
  /\ p2' = [p2 EXCEPT ![I][i] = div2(X2[I])[i]]
  /\ UNCHANGED <<c2,r2,rs2,X2>>

C2base(I,i) == 
  /\ ~ wrt(c2[I][i]) 
  /\ wrts(p2[I], depsB(X2[I],Dep_pc2,i))
  /\ isBase2(X2[I],p2[I],i)
  /\ c2' = [c2 EXCEPT ![I][i] = base2(X2[I],p2[I],i)]
  /\ UNCHANGED <<p2,r2,rs2,X2>> 

C2ini(I,i) == 
  /\ ~ wrt(X2[<<I[1],I[2] \o <<i>>>>]) 
  /\ wrts(p2[I], depsB(X2[I],Dep_pc2,i))
  /\ ~ isBase2(X2[I],p2[I],i)  
  /\ X2' = [X2 EXCEPT ![<<I[1],I[2] \o <<i>>>>] = p2[I][i]]
  /\ UNCHANGED <<p2,c2,r2,rs2>> 
             
C2end(I,i) == 
  /\ ~ wrt(c2[I][i])  
  /\ wrt(X2[<<I[1],I[2] \o <<i>>>>]) 
  /\ endB(<<I[1],I[2] \o <<i>>>>) 
  /\ c2' = [c2 EXCEPT ![I][i] = r2[<<I[1],I[2] \o <<i>>>>]]
  /\ UNCHANGED <<p2,r2,rs2,X2>>           

R2(I,i) == 
  /\ ~ redB(I,i) 
  /\ wrts(c2[I], depsB(X2[I],Dep_cr2,i))
  /\ i-1 >= 1 => redB(I,i-1)              \* dep r2(i-1) -> r2(i)
  /\ r2'  = [r2  EXCEPT ![I]    = Op2(@, fr2(X2[I],c2[I],i))]
  /\ rs2' = [rs2 EXCEPT ![I][i] = TRUE]       
  /\ UNCHANGED <<p2,c2,X2>> 
         
Done == /\ \A I \in WDIndexA : endA(I)
        /\ \A I \in WDIndexB : endB(I)
        /\ UNCHANGED <<in,vs1,X2,vs2>>
        /\ PrintT("Done: In = " \o ToString(X1[I0])
                 \o " - Out = " \o ToString(r1[I0]))     

StepA == /\ \E I \in WDIndexA : 
              \E i \in ItA(X1[I]) : \/ P1(I,i) 
                                    \/ C1base(I,i)
                                    \/ C1ini(I,i)
                                    \/ C1end(I,i)
                                    \/ R1ini(I,i)
                                    \/ R1end(I,i)
         /\ UNCHANGED <<in,vs2>>                       

StepB == /\ \E I \in WDIndexB : 
              \E i \in ItB(X2[I]) : \/ P2(I,i) 
                                    \/ C2base(I,i)
                                    \/ C2ini(I,i)
                                    \/ C2end(I,i)
                                    \/ R2(I,i)
         /\ UNCHANGED <<in,vs1>>                               
                               
Next == StepA \/ StepB \/ Done 

Spec == Init /\ [][Next]_<<in,vs1,vs2,X2>>

FairSpec == Spec /\ WF_<<vs1,X2>>(StepA) /\ WF_<<vs2,X2>>(StepB)

----------------------------------------------------------------------------

(* 
  PCR A properties
*)

TypeInvA == 
  /\ in  \in T
  /\ X1  \in [IndexA -> T \union {Undef}] /\ X1[I0] = in
  /\ p1  \in [IndexA -> StA(T)]
  /\ c1  \in [IndexA -> StA(D)]
  /\ r1  \in [IndexA -> D]
  /\ rs1 \in [IndexA -> [AssigA -> BOOLEAN]]          
    
PInvA == 
  \A I \in WDIndexA : \A i \in ItA(X1[I]) : 
    wrt(p1[I][i]) => p1[I][i] = div1(X1[I])[i]

CInv1A == 
  \A I \in WDIndexA : \A i \in ItA(X1[I]) : 
    wrt(c1[I][i]) /\ ~ isBase1(X1[I],p1[I],i) 
      => /\ wrts(p1[I],depsA(X1[I],Dep_pc1,i))
         /\ wrt(X1[I \o <<i>>])
         /\ endA(I \o <<i>>)
         /\ c1[I][i] = r1[I \o <<i>>]

CInv2A == 
  \A I \in WDIndexA : \A i \in ItA(X1[I]) : 
    wrt(c1[I][i]) /\ isBase1(X1[I],p1[I],i) 
      => /\ wrts(p1[I],depsA(X1[I],Dep_pc1,i))
         /\ c1[I][i] = base1(X1[I],p1[I],i)

RInv1A == 
  \A I \in WDIndexA : \A i \in ItA(X1[I]) : 
    redA(I,i) => /\ wrts(c1[I],depsA(X1[I],Dep_cr1,i)) 
                 /\ wrt(X2[<<I,<<i>>>>]) 
                 /\ endB(<<I,<<i>>>>)

RInv2A == 
  \A I \in WDIndexA :
    r1[I] = M1!BigOpP(1, uBnd1(X1[I]),
                      LAMBDA i : redA(I,i), 
                      LAMBDA i : fr1(X1[I],c1[I],i))

InvA == /\ TypeInvA
        /\ PInvA
        /\ CInv1A
        /\ CInv2A
        /\ RInv1A
        /\ RInv2A

CorrectnessA == \A I \in WDIndexA : endA(I) => r1[I] = A(X1[I])

TerminationA == <>(\A I \in WDIndexA : endA(I))
                             
(* 
  PCR B properties
*)

TypeInvB ==     
  /\ X2  \in [IndexB -> T2 \union {Undef}]
  /\ p2  \in [IndexB -> StB(T2)]
  /\ c2  \in [IndexB -> StB(D)]
  /\ r2  \in [IndexB -> D]
  /\ rs2 \in [IndexB -> [AssigB -> BOOLEAN]]
    
PInvB == 
  \A I \in WDIndexB : \A i \in ItB(X2[I]) : 
    wrt(p2[I][i]) => /\ p2[I][i] = div2(X2[I])[i]
                     /\ wrt(X2[I])

CInv1B == 
  \A I \in WDIndexB : \A i \in ItB(X2[I]) : 
    wrt(c2[I][i]) /\ ~ isBase2(X2[I],p2[I],i) 
      => /\ wrts(p2[I],depsB(X2[I],Dep_pc2,i))
         /\ wrt(X2[<<I[1],I[2] \o <<i>>>>])
         /\ endB(<<I[1],I[2] \o <<i>>>>)
         /\ c2[I][i] = r2[<<I[1],I[2] \o <<i>>>>]

CInv2B == 
  \A I \in WDIndexB : \A i \in ItB(X2[I]) : 
    wrt(c2[I][i]) /\ isBase2(X2[I],p2[I],i) 
      => /\ wrts(p2[I],depsB(X2[I],Dep_pc2,i))
         /\ c2[I][i] = base2(X2[I],p2[I],i)

RInv1B == 
  \A I \in WDIndexB : \A i \in ItB(X2[I]) : 
    redB(I,i)  => /\ wrts(c2[I],depsB(X2[I],Dep_cr2,i))
                  /\ \A k \in ItB(X2[I]) : k < i => redB(I,k) 

RInv2B == 
  \A I \in WDIndexB : \A i \in ItB(X2[I]) : 
    ~ redB(I,i) => r2[I] = M2!BigOpP(1, i-1,
                                     LAMBDA j : redB(I,j),  
                                     LAMBDA j : fr2(X2[I],c2[I],j))
                                                                                    
InvB == /\ TypeInvB
        /\ PInvB
        /\ CInv1B
        /\ CInv2B
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

PCR_DC == INSTANCE PCR_DC 
  WITH X <- X1, p <- p1, c <- c1, r <- r1, rs <- rs1,
       T <- T, D <- D,
       id <- id, Op <- Op1,
       div <- div1, isBase <- isBase1, base <- base1, fr <- fr1,      
       Dep_pc <- Dep_pc1, Dep_cr <- Dep_cr1

============================================================================
\* Modification History
\* Last modified Mon Sep 20 17:25:55 UYT 2021 by josedu
\* Last modified Thu Jul 08 01:14:51 GMT-03:00 2021 by JosEdu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
