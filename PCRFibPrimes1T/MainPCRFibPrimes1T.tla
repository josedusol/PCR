------------------------- MODULE MainPCRFibPrimes1T ------------------------

(*
   Main module for PCR FibPrimes1.
   
   This is an experimental alternative version where we replace the Undef
   and partial function concepts by explicitly defining and mantaining 
   function domains.
*)

EXTENDS Typedef, FiniteSets, TLC

VARIABLES N, cm1, im1, cm1Dom, vp1Dom, vc1Dom

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRFibPrimes1T WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1, 
  cm        <- cm1,
  cmDom     <- cm1Dom,
  vpDom     <- vp1Dom,
  vcDom     <- vc1Dom,
  im        <- im1   
                      
----------------------------------------------------------------------------

vars == <<N,cm1,im1,cm1Dom,vp1Dom,vc1Dom>>

Init == /\ N \in InType1
        /\ PCR1!pre(N)
        /\ cm1 = << >> :> PCR1!initCtx(N)
        /\ im1 = << >> :> PCR1!lowerBnd(N)
        /\ cm1Dom = { << >> }
        /\ vp1Dom = { }
        /\ vc1Dom = { }

(* PCR1 step on index I *)                  
Next1(I) == /\ PCR1!Next(I)
            /\ UNCHANGED <<N,cm1Dom>>     

Done == /\ \A I \in cm1Dom : PCR1!finished(I)
        /\ UNCHANGED vars       
\*        /\ PrintT("Done: In = " \o ToString(PCR1!in(<<>>))
\*                 \o " - Out = " \o ToString(PCR1!out(<<>>)))

Next == \/ \E I \in cm1Dom : Next1(I)
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
                      
fibonacci[n \in Nat] == 
  IF n < 2 
  THEN 1 
  ELSE fibonacci[n-1] + fibonacci[n-2]                

Solution(in) == LET fibValues == { fibonacci[n] : n \in 0..in }
                IN  Cardinality({ f \in fibValues : isPrime(f) })

TypeInv == /\ N \in InType1
           /\ cm1Dom \in SUBSET CtxIdType1
           /\ vp1Dom \in SUBSET IndexType1
           /\ vc1Dom \in SUBSET IndexType1
           /\ cm1 \in PCR1!CtxMap
           /\ im1 \in PCR1!IndexMap

IteratorType1 == 
  \A I \in cm1Dom :
    PCR1!iterator(I) = { n \in Nat : /\ PCR1!lowerBnd(N) <= n  
                                     /\ n <= PCR1!upperBnd(N) } 

IteratorType2 == \A I \in cm1Dom : PCR1!iterator(I) \subseteq IndexType1

ProducerType == \A I \in cm1Dom : 
                  \A i \in PCR1!iterator(I) : 
                    i < PCR1!i_p(I) => PCR1!v_p(I)[i] \in [v : VarPType1, r : Nat]  

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(N) )
  
Termination == <> PCR1!finished(<<>>) 

GTermination == [][ PCR1!finished(<<>>) <=> Done ]_vars

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 22:00:43 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
