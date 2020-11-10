------------------------- MODULE PCRFibPrimes1Main -------------------------

(*
   Main module for PCR FibPrimes1.
   
   This is an experimental alternative version where Undef is handled
   as a constant of the Spec.
*)

EXTENDS PCRFibPrimes1Types, FiniteSets, TLC

CONSTANT Undef

VARIABLES N, cm1, im1

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRFibPrimes1 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1, 
  cm        <- cm1,
  im        <- im1                      
                      
----------------------------------------------------------------------------

vars == <<N,cm1,im1>>

Init == /\ N \in InType1
        /\ PCR1!pre(N)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = << >> 
                     THEN PCR1!initCtx(N)
                     ELSE Undef]
        /\ im1 = [I \in CtxIdType1 |-> 
                     IF   I = << >> 
                     THEN PCR1!lowerBnd(N)
                     ELSE Undef]   

(* PCR1 step on index I *)                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED N     

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ UNCHANGED vars
\*        /\ PrintT("Done: In = " \o ToString(PCR1!in(<<>>))
\*                 \o " - Out = " \o ToString(PCR1!out(<<>>)))     

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ Done

Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))

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
           /\ cm1 \in PCR1!CtxMap
           /\ im1 \in PCR1!IndexMap

IteratorType1 == 
  \A I \in PCR1!CtxIndex :
    PCR1!iterator(I) = { n \in Nat : /\ PCR1!lowerBnd(N) <= n  
                                     /\ n <= PCR1!upperBnd(N) } 

IteratorType2 == \A I \in PCR1!CtxIndex : PCR1!iterator(I) \subseteq IndexType1

ProducerType == \A I \in PCR1!CtxIndex : \A i \in PCR1!iterator(I) : 
                    i < PCR1!i_p(I) => PCR1!written(PCR1!v_p(I), i)

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(N) )
  
Termination == <> PCR1!finished(<<>>) 

GTermination == [][ PCR1!finished(<<>>) <=> Done ]_vars

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 22:01:14 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
