------------------------ MODULE PCRIsPrimeSeqMain --------------------------

(*
   Main module for PCR IsPrimeSeq.
*)

EXTENDS PCRIsPrimeSeqTypes, FiniteSets

CONSTANT Undef

VARIABLES N, cm1, im1   

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRIsPrimeSeq WITH
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
        /\ cm1 = [i \in CtxIdType1 |-> 
                      IF   i = << >> 
                      THEN PCR1!initCtx(N)
                      ELSE Undef]                  
        /\ im1 = [i \in CtxIdType1 |-> 
                      IF   i = << >> 
                      THEN PCR1!lowerBnd(N)
                      ELSE Undef]
(* 
   PCR1 step at index I 
*)                          
Next1(i) == /\ cm1[i] # Undef
            /\ PCR1!Next(i)
            /\ UNCHANGED N              

Done == /\ \A i \in PCR1!CtxIndex : PCR1!finished(i)
        /\ UNCHANGED vars
\*        /\ PrintT("Done: In = " \o ToString(PCR1!in(<<>>))
\*                 \o " - Out = " \o ToString(PCR1!out(<<>>)))

Next == \/ \E i \in CtxIdType1 : Next1(i)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A i \in CtxIdType1 : WF_vars(Next1(i))

----------------------------------------------------------------------------

(* 
   Properties 
*)

isPrime(n) == LET div(k,m) == \E d \in 1..m : m = k * d
              IN n > 1 /\ ~ \E m \in 2..n-1 : div(m, n)
       
Solution(n) == isPrime(n)

TypeInv == /\ N \in InType1
           /\ cm1 \in PCR1!CtxMap
           /\ im1 \in PCR1!IndexMap

Correctness == []( PCR1!finished(<< >>) => PCR1!out(<< >>) = Solution(N) )
  
Termination == <> PCR1!finished(<< >>) 

\* This Spec is an implementation of PCRIsPrime!Spec. 
              
PCRIsPrime == INSTANCE PCRIsPrimeMain 
  WITH cm1 <- cm1
  
=============================================================================
\* Modification History
\* Last modified Mon Nov 09 21:51:56 UYT 2020 by josedu
\* Created Sat Aug 08 21:17:14 UYT 2020 by josedu
