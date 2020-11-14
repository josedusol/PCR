-------------------------- MODULE PCRKaratsubaMain -------------------------

(*
   Main module for PCR Karatsuba.
*)

EXTENDS PCRKaratsubaTypes, TLC

CONSTANT Undef

VARIABLES X1, X2, cm1 

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRKaratsuba WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarC1Type <- VarC1Type1,
  VarC2Type <- VarC2Type1,
  VarRType  <- VarRType1,  
  cm        <- cm1                     
           
----------------------------------------------------------------------------

vars == <<X1,X2,cm1>>

Init == /\ X1 \in In1Type1  
        /\ X2 \in In2Type1  
        /\ PCR1!pre(<<X1, X2>>)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(<<X1, X2>>)
                     ELSE Undef]                                                 

(* PCR1 step at index I *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED <<X1,X2>>    

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

Solution(in1, in2) == in1 * in2

TypeInv == /\ X1 \in In1Type1
           /\ X2 \in In2Type1
           /\ cm1 \in PCR1!CtxMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(X1, X2) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Sat Nov 14 18:24:04 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
