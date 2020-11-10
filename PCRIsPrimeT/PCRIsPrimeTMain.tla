------------------------- MODULE PCRIsPrimeTMain ---------------------------

(*
   Main module for PCR IsPrime.
   
   This is an experimental alternative version where we replace the Undef
   and partial function concepts by explicitly defining and mantaining 
   function domains.   
*)

EXTENDS PCRIsPrimeTTypes, FiniteSets, TLC

VARIABLES N, cm1, cm1Dom, vp1Dom, vc1Dom 

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRIsPrimeT WITH
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,   
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1, 
  cm        <- cm1,
  cmDom     <- cm1Dom,
  vpDom     <- vp1Dom,
  vcDom     <- vc1Dom

----------------------------------------------------------------------------

vars == <<N,cm1,cm1Dom,vp1Dom,vc1Dom>>

Init == /\ N \in InType1
        /\ PCR1!pre(N)    
        /\ cm1 = << >> :> PCR1!initCtx(N)
        /\ cm1Dom = { << >> }
        /\ vp1Dom = { }
        /\ vc1Dom = { }
        
(* PCR1 step at index I *)                   
Next1(I) == /\ PCR1!Next(I)
            /\ UNCHANGED <<N,cm1Dom>>              

Done == /\ \A I \in cm1Dom : PCR1!finished(I)
        /\ UNCHANGED vars
\*        /\ PrintT("Done: In = " \o ToString(PCR1!in(<<>>))
\*                 \o " - Out = " \o ToString(PCR1!out(<<>>)))

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A I \in CtxIdType1 : WF_vars(I \in cm1Dom /\ Next1(I))

----------------------------------------------------------------------------

(* 
   Properties 
*)

isPrime(n) == LET div(k,m) == \E d \in 1..m : m = k * d
              IN n > 1 /\ ~ \E m \in 2..n-1 : div(m, n)
       
Solution(n) == isPrime(n)

TypeInv == /\ N \in InType1
           /\ cm1Dom \in SUBSET CtxIdType1
           /\ vp1Dom \in SUBSET IndexType1
           /\ vc1Dom \in SUBSET IndexType1
           /\ cm1 \in PCR1!CtxMap

IteratorType == \A I \in cm1Dom : PCR1!iterator(I) \subseteq Nat

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(N) )
  
Termination == <> PCR1!finished(<<>>) 

GTermination == [][ PCR1!finished(<<>>) <=> Done ]_vars

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 21:47:28 UYT 2020 by josedu
\* Created Sat Aug 08 21:17:14 UYT 2020 by josedu
