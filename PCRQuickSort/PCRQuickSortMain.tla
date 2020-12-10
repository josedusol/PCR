-------------------------- MODULE PCRQuickSortMain -------------------------

(*
   Main module for PCR QuickSort.
*)

EXTENDS PCRQuickSortTypes, TLC

CONSTANT Undef

VARIABLES X, cm1 

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRQuickSort WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1                     
           
----------------------------------------------------------------------------

vars == <<X,cm1>>

Init == /\ X \in InType1  
        /\ PCR1!pre(X)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(X)
                     ELSE Undef]                                                 

(* PCR1 step at index I *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED X    

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ UNCHANGED vars     
        /\ PrintT("Done: In = " \o ToString(PCR1!in(<<>>))
                 \o " - Out = " \o ToString(PCR1!out(<<>>)))

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))
            
----------------------------------------------------------------------------

(* 
   Properties 
*)

Solution(in) == SortSeq(in, LAMBDA x,y : x < y)

TypeInv == /\ X \in InType1
           /\ cm1 \in PCR1!CtxMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(X) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Tue Nov 24 01:32:04 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
