------------------------------ MODULE PCR_A_it ------------------------------

(*
  PCR with iterative consumer over basic function.
   
  `.-----------------------------------------------------------------
    fun fp(x,p,i) = ...                //  fp : T x St(Tp) x N -> Tp  
    fun fc(y,x,p,i) = ...              //  fc : Tc x T x St(Tp) x N -> Tc
    fun fr(x,c,i) = ...                //  fr : T x St(Tc) x N -> D 
    fun cnd(s,k) = ...                 // cnd : St(Tc) x N -> Bool
 
    dep p(i-k) -> p(i)
    dep p(i[+/-]k) -> c(i)
    dep c(i[+/-]k) -> r(i)
   
    lbnd A = \x. ... 
    ubnd A = \x. ... 
    prop A = \i. ...   
   
    PCR A(x)                           // x \in T
      par
        p = produce fp x p
        c = iterate cnd fc (v0 x) x p
        r = reduce Op id (fr x c)      // r \in D 
  -----------------------------------------------------------------.'  
*)

EXTENDS AbstractAlgebra, Naturals, Sequences, Bags, SeqUtils, ArithUtils, TLC

----------------------------------------------------------------------------

(* 
  PCR constants and variables
*)

CONSTANTS I0, pre(_),             
          T, Tp, Tc, D, 
          id, Op(_,_), v0(_),
          lBnd(_), uBnd(_), prop(_),
          fp(_,_,_), fc(_,_,_,_), fr(_,_,_), gp(_,_), cnd(_,_),
          Dep_pp, Dep_pc, Dep_cr

VARIABLES in, X, p, c, r, rs, s
          
----------------------------------------------------------------------------

(* 
  General definitions
*)

Undef == CHOOSE x : x \notin UNION {T, Tp, Tc, D}  

last(S)      == S[Len(S)]
wrt(v)       == v # Undef
wrts(v,S)    == \A k \in S : wrt(v[k])
eqs(v1,v2,S) == \A k \in S : wrt(v1[k]) /\ v1[k] = v2[k]

----------------------------------------------------------------------------

(* 
  PCR A definitions and assumptions
*)

Index    == Seq(Nat)
Assig    == Nat
It(x)    == {i \in lBnd(x)..uBnd(x) : prop(i)}
WDIndex  == {I \in Index : wrt(X[I])}
St(R)    == [Assig -> R \union {Undef}] 
Iter(Z)  == Seq(Z) 
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
  /\ \A x \in T   : pre(x)  \in BOOLEAN
  /\ \A x \in T   : v0(x)   \in Tc
  /\ Dep_pp \in (SUBSET (Nat\{0})) \X (SUBSET {})
  /\ Dep_pc \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))  
  /\ Dep_cr \in (SUBSET (Nat\{0})) \X (SUBSET (Nat\{0}))   

AXIOM H_BFunType ==
  /\ \A x \in T, i \in Assig :
       /\ gp(x,i) \in Tp \union {Undef}
       /\ \A vp \in St(Tp) : fp(x,vp,i) \in Tp \union {Undef}    
       /\ \A vc \in St(Tc) : fr(x,vc,i) \in D  \union {Undef} 
       /\ \A vp \in St(Tp), y \in Tc : fc(y,x,vp,i) \in Tc \union {Undef}    
  /\ \A vs \in Iter(Tc), k \in Nat : cnd(vs,k) \in BOOLEAN

AXIOM H_BFunWD ==
  \A x \in T : \A i \in It(x) : 
    /\ gp(x,i) \in Tp
    /\ \A vp \in St(Tp) : wrts(vp,deps(x,Dep_pp,i)\{i}) => fp(x,vp,i) \in Tp
    /\ \A vc \in St(Tp) : wrts(vc,deps(x,Dep_cr,i))     => fr(x,vc,i) \in D 
    /\ \A vp \in St(Tp), y \in Tc : 
         wrts(vp,deps(x,Dep_pc,i)) => fc(y,x,vp,i) \in Tc           

AXIOM H_fpRelevance == 
  \A x \in T : \A i \in It(x), vp1 \in St(Tp), vp2 \in St(Tp) : 
    eqs(vp1,vp2,deps(x,Dep_pp,i)\{i}) => fp(x,vp1,i) = fp(x,vp2,i)

AXIOM H_fcRelevance == 
  \A y \in Tc : \A x \in T : \A i \in It(x), vp1 \in St(Tp), vp2 \in St(Tp) :
    eqs(vp1,vp2,deps(x,Dep_pc,i)) => fc(y,x,vp1,i) = fc(y,x,vp2,i)
           
AXIOM H_frRelevance == 
  \A x \in T : \A i \in It(x), vc1 \in St(Tp), vc2 \in St(Tp) : 
    eqs(vc1,vc1,deps(x,Dep_cr,i)) => fr(x,vc1,i) = fr(x,vc2,i)  

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

RECURSIVE iter(_,_,_,_)
iter(vs,x,vp,i) == IF cnd(vs,Len(vs)) 
                   THEN vs 
                   ELSE iter(vs \o <<fc(last(vs),x,vp,i)>>, x, vp, i)

(* 
  Alternatively, iter defined as a recursive function:

  iter[vs \in Iter(Tc), x \in T, vp \in St(Tp), i \in Assig] == 
    IF cnd(vs,Len(vs)) 
    THEN vs 
    ELSE iter[vs \o <<fc(lst(vs),x,vp,i)>>, x, vp, i]
*)

Gp(x)    == [i \in Assig |-> gp(x,i)] 
Fr(x,vc) == [i \in Assig |-> fr(x,vc,i)] 
Fc(x,vp) == [i \in Assig |-> last(iter(<<v0(x)>>,x,vp,i))]

A(x) == M!BigOpP(lBnd(x), uBnd(x), prop, LAMBDA i : Fr(x,Fc(x,Gp(x)))[i])

----------------------------------------------------------------------------

(* 
  Operational specification
*)

vs == <<X,p,c,r,rs,s>>

Init == /\ in \in T /\ pre(in)      
        /\ X  = [I \in Index |-> IF I = I0 THEN in ELSE Undef]    
        /\ p  = [I \in Index |-> [i \in Assig |-> Undef]]
        /\ c  = [I \in Index |-> [i \in Assig |-> Undef]]  
        /\ s  = [I \in Index |-> [i \in Assig |-> Undef]] 
        /\ rs = [I \in Index |-> [i \in Assig |-> FALSE]]
        /\ r  = [I \in Index |-> id]
              
P(I,i) ==  
  /\ ~ wrt(p[I][i]) 
  /\ wrts(p[I], deps(X[I],Dep_pp,i)\{i})
  /\ p' = [p EXCEPT ![I][i] = fp(X[I],p[I],i)]
  /\ UNCHANGED <<X,c,r,rs,s>>

Cstart(I,i) ==   
  /\ ~ wrt(s[I][i]) 
  /\ wrts(p[I], deps(X[I],Dep_pc,i))
  /\ s' = [s EXCEPT ![I][i] = <<v0(X[I])>>]
  /\ UNCHANGED <<X,p,c,r,rs>>

Cstep(I,i) == 
  /\ wrt(s[I][i])
  /\ ~ cnd(s[I][i], Len(s[I][i]))
  /\ s' = [s EXCEPT ![I][i] = @ \o <<fc(last(s[I][i]),X[I],p[I],i)>>]
  /\ UNCHANGED <<X,p,c,r,rs>>
             
Cend(I,i) == 
  /\ ~ wrt(c[I][i])
  /\ wrt(s[I][i])
  /\ cnd(s[I][i], Len(s[I][i]))  
  /\ c' = [c EXCEPT ![I][i] = last(s[I][i])]
  /\ UNCHANGED <<X,p,r,rs,s>>

R(I,i) == 
  /\ ~ red(I,i) 
  /\ wrts(c[I], deps(X[I],Dep_cr,i))
  /\ r'  = [r   EXCEPT ![I]   = Op(@, fr(X[I],c[I],i))]
  /\ rs' = [rs EXCEPT ![I][i] = TRUE] 
  /\ UNCHANGED <<X,p,c,s>>      
 
Done == /\ \A I \in WDIndex : end(I)
        /\ UNCHANGED <<in,vs>>
\*        /\ PrintT("Done: In = " \o ToString(X[I0])
\*                 \o " - Out = " \o ToString(r[I0]))    

Step == /\ \E I \in WDIndex :
             \E i \in It(X[I]) : \/ P(I,i) 
                                 \/ Cstart(I,i)
                                 \/ Cstep(I,i)
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

IndexInv == WDIndex = { I0 }
                          
TypeInv == 
  /\ in \in T
  /\ X  \in [Index -> T \union {Undef}] /\ X[I0] = in
  /\ p  \in [Index -> St(Tp)]
  /\ c  \in [Index -> St(Tc)]
  /\ s  \in [Index -> St(Iter(Tc))]
  /\ r  \in [Index -> D]
  /\ rs \in [Index -> [Assig -> BOOLEAN]]
         
PInv == 
  \A i \in It(X[I0]) : 
    wrt(p[I0][i]) => /\ wrts(p[I0],deps(X[I0],Dep_pp,i))
                     /\ p[I0][i] = gp(X[I0],i) 
                     
CInv == 
  \A i \in It(X[I0]) : 
    wrt(c[I0][i]) => /\ wrts(p[I0],deps(X[I0],Dep_pc,i))
                     /\ c[I0][i] = last(iter(<<v0(X[I0])>>,X[I0],p[I0],i))
                     
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
             
Correctness == end(I0) => r[I0] = A(X[I0])

Termination == <> end(I0)          

(* 
  Refinement
*)

fcS(x,vp,i) == last(iter(<<v0(x)>>,x,vp,i))

PCR_A == INSTANCE PCR_A 
  WITH X <- X, p <- p, c <- c, r <- r, rs <- rs,
       T <- T, Tp <- Tp, Tc <- Tc, D <- D, 
       id <- id, Op <- Op,
       lBnd <- lBnd, uBnd <- uBnd, prop <- prop,                 
       fp <- fp, fc <- fcS, fr <- fr, gp <- gp,      
       Dep_pp <- Dep_pp, Dep_pc <- Dep_pc, Dep_cr <- Dep_cr

============================================================================
\* Modification History
\* Last modified Sun Sep 12 15:10:22 UYT 2021 by josedu
\* Last modified Wed Jul 07 19:43:42 GMT-03:00 2021 by JosEdu
\* Last modified Fri Jul 17 16:28:02 UYT 2020 by josed
\* Created Mon Jul 06 13:03:07 UYT 2020 by josed
