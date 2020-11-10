-------------------------- MODULE PCRFibRecMain ----------------------------

(*
   Main module for PCR FibRec.
*)

EXTENDS PCRFibRecTypes, FiniteSets, TLC

CONSTANT Undef

VARIABLES N, cm1

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRFibRec WITH
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,   
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1, 
  cm        <- cm1

----------------------------------------------------------------------------

vars == <<N,cm1>>

Init == /\ N \in InType1
        /\ PCR1!pre(N) 
        /\ cm1 = [I \in CtxIdType1 |-> 
                      IF   I = <<>> 
                      THEN PCR1!initCtx(N)
                      ELSE Undef]                          
                                 
(* PCR1 step at index I *)                           
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

fibonacci[n \in Nat] == 
  IF n < 2 
  THEN 1 
  ELSE fibonacci[n-1] + fibonacci[n-2]                

Solution(in) == fibonacci[in]

TypeInv == /\ N \in InType1
           /\ cm1 \in PCR1!CtxMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(N) )
  
Termination == <> PCR1!finished(<<>>) 
  
=============================================================================
\* Modification History
\* Last modified Mon Nov 09 21:54:40 UYT 2020 by josedu
\* Created Sat Aug 08 21:17:14 UYT 2020 by josedu
