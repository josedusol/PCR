------------------------ MODULE MainPCRFibRec --------------------------

(*
   Main module for PCR FibRec.
*)

EXTENDS Typedef, FiniteSets, TLC

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

Undef == PCR1!Undef

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
\*        /\ PrintT("ret " \o ToString(PCR1!in(<<0>>)) \o " : " \o ToString(PCR1!Out(<<0>>)))

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
\* Last modified Thu Oct 29 14:39:12 UYT 2020 by josedu
\* Created Sat Aug 08 21:17:14 UYT 2020 by josedu
