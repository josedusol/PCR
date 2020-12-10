-------------------------- MODULE PCRMergeSort2RMain -----------------------

(*
   Main module for PCR MergeSort2.
*)

EXTENDS PCRMergeSort2RTypes, TLC

CONSTANT Undef

VARIABLES X, cm1, cm2 

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRMergeSort2R WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1,
  cm2       <- cm2                     

PCR2 == INSTANCE PCRMerge WITH 
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,  
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  cm        <- cm2   
           
----------------------------------------------------------------------------

vars == <<X,cm1,cm2>>

Init == /\ X \in InType1  
        /\ PCR1!pre(X)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(X)
                     ELSE Undef]          
        /\ cm2 = [I \in CtxIdType2 |-> Undef]                                                   

(* PCR1 step at index I *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED X    

(* PCR2 step at index I  *)                                                  
Next2(I) == /\ cm2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<X,cm1>>               

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ \A I \in PCR2!CtxIndex : PCR2!finished(I)
        /\ UNCHANGED vars         
        /\ PrintT("Done: In = " \o ToString(PCR1!in(<<>>))
                 \o " - Out = " \o ToString(PCR1!out(<<>>)))

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ \E I \in CtxIdType2 : Next2(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))
            /\ \A I \in CtxIdType2 : WF_vars(Next2(I))
            
----------------------------------------------------------------------------

(* 
   Properties 
*)

Solution(in) == SortSeq(in, LAMBDA x,y : x < y)

TypeInv == /\ X \in InType1
           /\ cm1 \in PCR1!CtxMap
           /\ cm2 \in PCR2!CtxMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(X) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) <=> Done ]_vars

=============================================================================
\* Modification History
\* Last modified Sat Nov 21 17:11:59 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
