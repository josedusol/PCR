-------------------------- MODULE MainPCRNQueensFirst ------------------------

(*
   Main module for PCR NQueensFirst.
*)

EXTENDS Typedef, Functions, FiniteSets, TLC

VARIABLES B, cm1    

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRNQueensFirst WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1                      
           
Undef == PCR1!Undef           
           
----------------------------------------------------------------------------

vars == <<B,cm1>>

Init == /\ B \in InType1
        /\ PCR1!pre(B)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(B)
                     ELSE Undef]                                                

(* PCR1 step at index I  *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED B    

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ UNCHANGED vars         
\*        /\ PrintT("done " \o " : " \o ToString(Cardinality(DOMAIN [I \in PCR1!CtxIndex |-> map[I]] )))    
        /\ PrintT("done " \o " : " \o ToString(PCR1!out(<<>>)))       

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))
            
----------------------------------------------------------------------------

(* 
   Properties 
*)

Solution(in) == CASE Len(in) = 0      -> { Null }
                  [] Len(in) = 1      -> { <<1>> }
                  [] Len(in) \in 2..3 -> { Null }
                  [] Len(in) = 4      -> { <<3,1,4,2>>, <<2,4,1,3>> }
               \* [] Len(in) = 5      -> { ... 10 solutions ... } 

TypeInv == /\ B \in InType1
           /\ cm1 \in PCR1!CtxMap
           
Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) \in Solution(B) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 20:55:48 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
