------------------------------- MODULE PCR_A -------------------------------

(*
  Basic PCR.
   
  `.----------------------------------------------------------------- 
    fun fp(x,p,i) = ...               // fp : T x St(Tp) x N -> Tp 
    fun fc(x,p,i) = ...               // fc : T x St(Tp) x N -> Tc
    fun fr(x,c,i) = ...               // fr : T x St(Tc) x N -> D  
   
    dep p(i-k) -> p(i)
    dep p(i[+/-]k) -> c(i)
    dep c(i[+/-]k) -> r(i)
   
    lbnd A = \x. ...
    ubnd A = \x. ... 
    prop A = \i. ... 
   
    PCR A(x)                          // x \in T
      par
        p = produce fp x p
        c = consume fc x p
        r = reduce  Op id (fr x c)    // r \in D 
  -----------------------------------------------------------------.'  
*)

EXTENDS AbstractAlgebra, Naturals, Sequences, Bags, SeqUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  PCR constants and variables
*)

CONSTANTS I0, pre(_),             
          T, Tp, Tc, D,
          id, Op(_,_),
          lBnd(_), uBnd(_), prop(_),
          fp(_,_,_), fc(_,_,_), fr(_,_,_), gp(_,_),
          Dep_pp, Dep_pc, Dep_cr

VARIABLES in, X, p, c, r, rs
          
----------------------------------------------------------------------------

(* 
  General definitions
*)

Undef == CHOOSE x : x \notin UNION {T, Tp, Tc, D} 

wrt(v)       == v # Undef
wrts(v,S)    == \A k \in S : wrt(v[k])
eqs(v1,v2,S) == \A k \in S : wrt(v1[k]) /\ v1[k] = v2[k]

----------------------------------------------------------------------------

(* 
  PCR definitions and assumptions
*)

Index    == Seq(Nat)
Assig    == Nat
St(R)    == [Assig -> R \union {Undef}]
WDIndex  == {I \in Index : wrt(X[I])}
It(x)    == {i \in lBnd(x)..uBnd(x) : prop(i)}
red(I,i) == rs[I][i]
end(I)   == \A i \in It(X[I]) : red(I,i)

deps(x,d,i) == 
         {i-k : k \in {k \in d[1] : i-k >= lBnd(x) /\ prop(i-k)}} 
  \union {i} 
  \union {i+k : k \in {k \in d[2] : i+k <= uBnd(x) /\ prop(i+k)}} 
  
AXIOM H_Type ==
  /\ I0   \in Index
  /\ \A x \in T   : lBnd(x) \in Nat
  /\ \A x \in T   : uBnd(x) \in Nat
  /\ \A i \in Nat : prop(i) \in BOOLEAN
  /\ \A x \in T   : pre(x) \in BOOLEAN
  /\ Dep_pp \in (SUBSET (Nat\{0})) \X (SUBSET {})
  /\ Dep_pc \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))
  /\ Dep_cr \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))   

AXIOM H_BFunType ==
  \A x \in T, i \in Assig :
    /\ gp(x,i) \in Tp \union {Undef}
    /\ \A vp \in St(Tp) : fp(x,vp,i) \in Tp \union {Undef}
    /\ \A vp \in St(Tp) : fc(x,vp,i) \in Tc \union {Undef}
    /\ \A vc \in St(Tc) : fr(x,vc,i) \in D  \union {Undef}

AXIOM H_BFunWD ==
  \A x \in T : \A i \in It(x) :  
    /\ gp(x,i) \in Tp
    /\ \A vp \in St(Tp) : wrts(vp,deps(x,Dep_pp,i)\{i}) => fp(x,vp,i) \in Tp
    /\ \A vp \in St(Tp) : wrts(vp,deps(x,Dep_pc,i))     => fc(x,vp,i) \in Tc
    /\ \A vc \in St(Tc) : wrts(vc,deps(x,Dep_cr,i))     => fr(x,vc,i) \in D

AXIOM H_fpRelevance == 
  \A x \in T : \A i \in It(x), vp1 \in St(Tp), vp2 \in St(Tp) :
    eqs(vp1,vp2,deps(x,Dep_pp,i)\{i}) => fp(x,vp1,i) = fp(x,vp2,i)
      
AXIOM H_fcRelevance == 
  \A x \in T : \A i \in It(x), vp1 \in St(Tp), vp2 \in St(Tp) :
    eqs(vp1,vp2,deps(x,Dep_pc,i)) => fc(x,vp1,i) = fc(x,vp2,i)      

AXIOM H_frRelevance == 
  \A x \in T : \A i \in It(x), vc1 \in St(Tc), vc2 \in St(Tc) : 
    eqs(vc1,vc2,deps(x,Dep_cr,i)) => fr(x,vc1,i) = fr(x,vc2,i)

LEMMA H_ProdEqInv ==
  \A x \in T : \A i \in It(x) :
    wrt(p[I0][i]) => fp(x,p[I0],i) = gp(x,i)

----------------------------------------------------------------------------

(* 
  Functional specification
*)

M == INSTANCE AbelianMonoidBigOp
  WITH D <- D, Id <- id, \otimes <- Op 

AXIOM H_Algebra == AbelianMonoid(D, id, Op)

Gp(x)    == [i \in Assig |-> gp(x,i)] 
Fc(x,vp) == [i \in Assig |-> fc(x,vp,i)] 
Fr(x,vc) == [i \in Assig |-> fr(x,vc,i)] 

A(x) == M!BigOpP(lBnd(x), uBnd(x), prop, LAMBDA i : Fr(x,Fc(x,Gp(x)))[i])

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
  /\ wrts(p[I], deps(X[I],Dep_pp,i)\{i})
  /\ p' = [p EXCEPT ![I][i] = fp(X[I],p[I],i)]
  /\ UNCHANGED <<X,c,r,rs>>

C(I,i) == 
  /\ ~ wrt(c[I][i]) 
  /\ wrts(p[I], deps(X[I],Dep_pc,i))
  /\ c' = [c EXCEPT ![I][i] = fc(X[I],p[I],i)]
  /\ UNCHANGED <<X,p,r,rs>> 

R(I,i) == 
  /\ ~ red(I,i)
  /\ wrts(c[I], deps(X[I],Dep_cr,i)) 
  /\ r'  = [r  EXCEPT ![I]    = Op(@, fr(X[I],c[I],i))]
  /\ rs' = [rs EXCEPT ![I][i] = TRUE]
  /\ UNCHANGED <<X,p,c>>       
         
Done == /\ \A I \in WDIndex : end(I)
        /\ UNCHANGED <<in,vs>>
        /\ PrintT("Done: In = " \o ToString(X[I0])
                 \o " - Out = " \o ToString(r[I0]))     

Step == /\ \E I \in WDIndex : 
             \E i \in It(X[I]) : \/ P(I,i) 
                                 \/ C(I,i)
                                 \/ R(I,i)
        /\ UNCHANGED in                      
      
Next == Step \/ Done

Spec == Init /\ [][Next]_<<in,vs>>

FairSpec == Spec /\ WF_vs(Step)

----------------------------------------------------------------------------

(* 
  Properties
*)
            
IndexInv == WDIndex = { I0 }
                          
TypeInv == 
  /\ in \in T
  /\ X  \in [Index -> T \union {Undef}] /\ X[I0] = in
  /\ p  \in [Index -> St(Tp)]
  /\ c  \in [Index -> St(Tc)]
  /\ r  \in [Index -> D]
  /\ rs \in [Index -> [Assig -> BOOLEAN]]
         
PInv == 
  \A i \in It(X[I0]) : 
    wrt(p[I0][i]) => /\ wrts(p[I0],deps(X[I0],Dep_pp,i))
                     /\ p[I0][i] = fp(X[I0],p[I0],i)
                     
CInv == 
  \A i \in It(X[I0]) : 
    wrt(c[I0][i]) => /\ wrts(p[I0],deps(X[I0],Dep_pc,i))
                     /\ c[I0][i] = fc(X[I0],p[I0],i)

RInv1 == 
  \A i \in It(X[I0]) : 
    red(I0,i) => wrts(c[I0],deps(X[I0],Dep_cr,i)) 
                           
RInv2 == 
  r[I0] = M!BigOpP(lBnd(X[I0]), uBnd(X[I0]),
                   LAMBDA i : prop(i) /\ red(I0,i), 
                   LAMBDA i : fr(X[I0],c[I0],i))                       
                                        
Inv == /\ TypeInv
       /\ IndexInv
       /\ PInv
       /\ CInv
       /\ RInv1
       /\ RInv2

ISpec == Inv /\ [][Next]_<<vs>>
             
Correctness == end(I0) => r[I0] = A(X[I0])

Termination == <> end(I0)          

(* 
  Refinement
*)

inS  == X[I0]
outS == IF end(I0) THEN r[I0] ELSE id

A1step == INSTANCE PCR_A1step
  WITH in <- inS, out <- outS,
       T <- T, D <- D, 
       id <- id, Op <- Op,
       lBnd <- lBnd, uBnd <- uBnd, prop <- prop,       
       fp <- fp, fc <- fc, fr <- fr, gp <- gp

============================================================================
\* Modification History
\* Last modified Sun Sep 12 15:09:49 UYT 2021 by josedu
\* Last modified Thu Jul 08 02:51:43 GMT-03:00 2021 by JosEdu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
