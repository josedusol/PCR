------------------------ MODULE PCRIsPrimeRecMain --------------------------

(*
   Main module for PCR IsPrimeRec.
*)

EXTENDS PCRIsPrimeRecTypes, FiniteSets

CONSTANT Undef

VARIABLES N, M, cm1

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRIsPrimeRec WITH
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,   
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1, 
  cm        <- cm1

----------------------------------------------------------------------------

vars == <<N,M,cm1>>

Init == /\ N \in In1Type1
        /\ M \in In2Type1
        /\ PCR1!pre(<<N,M>>) 
        /\ cm1 = [I \in CtxIdType1 |-> 
                      IF   I = <<>> 
                      THEN PCR1!initCtx(<<N,M>>)
                      ELSE Undef]                  

(* 
   PCR1 step at index I 
*)                           
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED <<N,M>>              

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
       
Solution(n) == isPrime(n)

TypeInv == /\ N \in In1Type1
           /\ M \in In2Type1
           /\ cm1 \in PCR1!CtxMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(N) )
  
Termination == <> PCR1!finished(<<>>) 
  
=============================================================================
\* Modification History
\* Last modified Mon Nov 09 21:52:26 UYT 2020 by josedu
\* Created Sat Aug 08 21:17:14 UYT 2020 by josedu
