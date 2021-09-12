---------------------------- MODULE PCR_DCrLeft ----------------------------

(*
  Divide-and-conquer PCR with left reducer.
   
  `.-----------------------------------------------------------------
    fun div(x)         = ...                     //    div : T -> Seq(T)   
    fun isBase(x,p,i)  = ...                     // isBase : T x St(T) x N -> Bool 
    fun base(x,p,i)    = ...                     //   base : T x St(T) x N -> D
    fun fr(x,c,i)      = ...                     //     fr : T x St(D) x N -> D
     
    fun iterDiv(x,p,i)    = div(x)[i]     
    fun subproblem(x,p,i) = if isBase(x,p,i)  
                            then base(x,p,i)
                            else DC(p)
    fun conquer(r,x,c,i) = Op(r, fr(x,c,i))

    dep p(i[+/-]k) -> c(i)
    dep c(i[+/-]k) -> r(i)
    dep r(i-1) -> r(i) 
   
    lbnd DC = \x. 1 
    ubnd DC = \x. len(div(x))
   
    PCR DC(x)                                    // x \in T
      par
        p = produce iterDiv x p
        c = consume subproblem x p
        r = reduce conquer id x c                // r \in D
  -----------------------------------------------------------------.'  
*)

EXTENDS AbstractAlgebra, Naturals, Sequences, Bags, SeqUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  PCR constants and variables 
*)

CONSTANTS I0, pre(_),             
          T, D,
          id, Op(_,_),
          div(_), isBase(_,_,_), base(_,_,_), fr(_,_,_),
          Dep_pc, Dep_cr   

VARIABLES in, X, p, c, r, rs           
         
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
  PCR definitions and assumptions
*)

Index    == Seq(Nat)
Assig    == Nat
uBnd(x)  == Len(div(x))
It(x)    == 1..uBnd(x)
WDIndex  == {I \in Index : wrt(X[I])}
St(R)    == [Assig -> R \union {Undef}] 
red(I,i) == rs[I][i]
end(I)   == \A i \in It(X[I]) : red(I,i)

deps(x,d,i) == 
         {i-k : k \in {k \in d[1] : i-k >= 1}} 
  \union {i} 
  \union {i+k : k \in {k \in d[2] : i+k <= uBnd(x)}} 

AXIOM H_Type ==
  /\ I0   \in Index
  /\ \A x \in T : uBnd(x) \in Nat
  /\ \A x \in T : pre(x) \in BOOLEAN
  /\ Dep_pc \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))
  /\ Dep_cr \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))   

AXIOM H_BFunType ==
  \A x \in T, i \in Assig :
    /\ div(x) \in Seq(T) \union {Undef}
    /\ \A vp \in St(T) : isBase(x,vp,i) \in BOOLEAN \union {Undef}
    /\ \A vp \in St(T) : base(x,vp,i)   \in D  \union {Undef}
    /\ \A vc \in St(D) : fr(x,vc,i)     \in D  \union {Undef}

AXIOM H_BFunWD ==
  \A x \in T : \A i \in It(x) :
    /\ div(x) \in Seq(T) 
    /\ \A vp \in St(T) : wrts(vp,deps(x,Dep_pc,i)) => isBase(x,vp,i) \in BOOLEAN
    /\ \A vp \in St(T) : wrts(vp,deps(x,Dep_pc,i)) => base(x,vp,i) \in D
    /\ \A vc \in St(D) : wrts(vc,deps(x,Dep_cr,i)) => fr(x,vc,i) \in D  

AXIOM H_fcRelevance == 
  \A x \in T : \A i \in It(x), vp1 \in St(T), vp2 \in St(T) :
    eqs(vp1,vp2,deps(x,Dep_pc,i)) => isBase(x,vp1,i) = isBase(x,vp2,i)
      
AXIOM H_baseRelevance == 
  \A x \in T : \A i \in It(x), vp1 \in St(T), vp2 \in St(T) :
    eqs(vp1,vp2,deps(x,Dep_pc,i)) => base(x,vp1,i) = base(x,vp2,i)      

AXIOM H_frRelevance == 
  \A x \in T : \A i \in It(x), vc1 \in St(D), vc2 \in St(D) :
    eqs(vc1,vc2,deps(x,Dep_cr,i)) => fr(x,vc1,i) = fr(x,vc2,i) 

----------------------------------------------------------------------------

(* 
  Functional specification
*)

M == INSTANCE MonoidBigOp 
  WITH D <- D, Id <- id, \otimes <- Op

AXIOM H_Algebra == Monoid(D, id, Op)

Fr(x,vc) == [i \in Assig |-> fr(x,vc,i)]

RECURSIVE DC(_)
DC(x) == M!BigOp(1, uBnd(x), 
                 LAMBDA i : Fr(x,[k \in Assig |-> IF isBase(x,div(x),k)   
                                                  THEN base(x,div(x),k)
                                                  ELSE DC(div(x)[k])])[i])
(* 
  Alternatively, DC defined as a recursive function:

  DC[x \in T] == 
    M!BigOp(1, uBnd(x), 
            LAMBDA i : Fr(x,[k \in Assig |-> IF isBase(x,div(x),k)   
                                             THEN base(x,div(x),k)
                                             ELSE DC[div(x)[k]]])[i])
*) 

----------------------------------------------------------------------------

(* 
  Operational specification
*)

vs == <<X,p,c,r,rs>>

Init == /\ in \in T /\ pre(in)    
        /\ X  = [I \in Index |-> IF I = I0 THEN in ELSE Undef]
        /\ p  = [I \in Index |-> [i \in Assig |-> Undef]]
        /\ c  = [I \in Index |-> [i \in Assig |-> Undef]]  
        /\ rs = [I \in Index |-> [i \in Assig |-> FALSE]]
        /\ r  = [I \in Index |-> id]

P(I,i) == 
  /\ ~ wrt(p[I][i]) 
  /\ p' = [p EXCEPT ![I][i] = div(X[I])[i]]
  /\ UNCHANGED <<X,c,r,rs>>

Cbase(I,i) == 
  /\ ~ wrt(c[I][i]) 
  /\ wrts(p[I], deps(X[I],Dep_pc,i))
  /\ isBase(X[I],p[I],i) 
  /\ c' = [c EXCEPT ![I][i] = base(X[I],p[I],i)]
  /\ UNCHANGED <<X,p,r,rs>> 

Cini(I,i) == 
  /\ ~ wrt(X[I \o <<i>>])
  /\ wrts(p[I], deps(X[I],Dep_pc,i))    
  /\ ~ isBase(X[I],p[I],i)
  /\ X' = [X EXCEPT ![I \o <<i>>] = p[I][i]]
  /\ UNCHANGED <<p,c,r,rs>> 
             
Cend(I,i) == 
  /\ ~ wrt(c[I][i]) 
  /\ wrt(X[I \o <<i>>]) 
  /\ end(I \o <<i>>)  
  /\ c' = [c EXCEPT ![I][i] = r[I \o <<i>>]]
  /\ UNCHANGED <<X,p,r,rs>>           

R(I,i) == 
  /\ ~ red(I,i) 
  /\ wrts(c[I], deps(X[I],Dep_cr,i))
  /\ i-1 >= 1 => red(I,i-1)            \* dep r(i-1) -> r(i)
  /\ r'  = [r  EXCEPT ![I]    = Op(@, fr(X[I],c[I],i))]
  /\ rs' = [rs EXCEPT ![I][i] = TRUE]   
  /\ UNCHANGED <<X,p,c>>       
         
Done == /\ \A I \in WDIndex : end(I)
        /\ UNCHANGED <<in,vs>>
\*        /\ PrintT("Done: In = " \o ToString(X[I0])
\*                 \o " - Out = " \o ToString(r[I0]))     

Step == /\ \E I \in WDIndex : 
             \E i \in It(X[I]) : \/ P(I,i) 
                                 \/ Cbase(I,i)
                                 \/ Cini(I,i)
                                 \/ Cend(I,i)
                                 \/ R(I,i)
        /\ UNCHANGED in                      
                               
Next == Step \/ Done 

Spec == Init /\ [][Next]_<<in,vs>>

FairSpec == Spec /\ WF_vs(Step)

----------------------------------------------------------------------------

(* 
  Properties
*)

TypeInv == 
  /\ in \in T
  /\ X  \in [Index -> T \union {Undef}] /\ X[I0] = in
  /\ p  \in [Index -> St(T)]
  /\ c  \in [Index -> St(D)]
  /\ r  \in [Index -> D]
  /\ rs \in [Index -> [Assig -> BOOLEAN]]

PInv == 
  \A I \in WDIndex : \A i \in It(X[I]) : 
    wrt(p[I][i]) => p[I][i] = div(X[I])[i]

CInv1 == 
  \A I \in WDIndex : \A i \in It(X[I]) : 
    wrt(c[I][i]) /\ ~ isBase(X[I],p[I],i) 
      => /\ wrts(p[I],deps(X[I],Dep_pc,i))
         /\ wrt(X[I \o <<i>>])
         /\ c[I][i] = r[I \o <<i>>]        

CInv2 == 
  \A I \in WDIndex : \A i \in It(X[I]) : 
    wrt(c[I][i]) /\ isBase(X[I],p[I],i) 
      => /\ wrts(p[I],deps(X[I],Dep_pc,i))
         /\ c[I][i] = base(X[I],p[I],i)    

RInv1 == 
  \A I \in WDIndex : \A i \in It(X[I]) : 
    red(I,i) => /\ wrts(c[I],deps(X[I],Dep_cr,i)) 
                /\ \A k \in It(X[I]) : k < i => red(I,k)                            

RInv2 == 
  \A I \in WDIndex : \A i \in It(X[I]) : 
    ~ red(I,i) => r[I] = M!BigOpP(1, i-1,
                                  LAMBDA j : red(I,j),  
                                  LAMBDA j : fr(X[I],c[I],j))
                                                                                    
Inv == /\ TypeInv
       /\ PInv
       /\ CInv1
       /\ CInv2
       /\ RInv1
       /\ RInv2
             
Correctness == \A I \in WDIndex : end(I) => r[I] = DC(X[I])

Termination == <> \A I \in WDIndex : end(I)         

(* 
  Refinement
*)

PCR_DC == INSTANCE PCR_DC 
  WITH X <- X, p <- p, c <- c, r <- r, rs <- rs,
       T <- T, D <- D, 
       id <- id, Op <- Op,        
       div <- div, isBase <- isBase, base <- base, fr <- fr,       
       Dep_pc <- Dep_pc, Dep_cr <- Dep_cr

============================================================================
\* Modification History
\* Last modified Wed Sep 08 18:30:07 UYT 2021 by josedu
\* Last modified Thu Jul 08 01:02:39 GMT-03:00 2021 by JosEdu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
