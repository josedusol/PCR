------------------------ MODULE PCRNQueensFirstITMain ----------------------

(*
   Main module for PCR NQueensFirstIT.
*)

EXTENDS PCRNQueensFirstITTypes, Functions, FiniteSets, TLC

CONSTANT Undef

VARIABLES X, cm1, cm2, ym 

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRNQueensFirstIT WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1,
  cm2       <- cm2,
  ym        <- ym                      

PCR2 == INSTANCE PCRNQueensFirstITStep WITH 
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,  
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  cm        <- cm2     
           
----------------------------------------------------------------------------

vars == <<X,cm1,cm2,ym>>

Init == /\ X \in InType1
        /\ PCR1!pre(X)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(X)
                     ELSE Undef]  
        /\ ym  = [I \in CtxIdType1 |-> Undef]            
        /\ cm2 = [I \in CtxIdType2 |-> Undef]                                                       

(* PCR1 step at index I  *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED X         

(* PCR2 step at index I  *)                                                  
Next2(I) == /\ cm2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<X,cm1,ym>>               

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ \A I \in PCR2!CtxIndex : PCR2!finished(I)
        /\ UNCHANGED vars         
\*        /\ PrintT("Done: In = " \o ToString(PCR1!in(<<>>))
\*                 \o " - Out = " \o ToString(PCR1!out(<<>>)))

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

Solution(in) == CASE Len(in) = 0      -> { <<>> }
                  [] Len(in) = 1      -> { <<1>> }
                  [] Len(in) \in 2..3 -> { }
                  [] Len(in) = 4      -> { <<3,1,4,2>>, <<2,4,1,3>> }
                  [] Len(in) = 5      -> { <<1, 3, 5, 2, 4>>,  
                                           <<1, 4, 2, 5, 3>>,
                                           <<2, 4, 1, 3, 5>>,
                                           <<2, 5, 3, 1, 4>>,
                                           <<3, 1, 4, 2, 5>>,
                                           <<3, 5, 2, 4, 1>>,                                         
                                           <<4, 1, 3, 5, 2>>,
                                           <<4, 2, 5, 3, 1>>, 
                                           <<5, 2, 4, 1, 3>>,
                                           <<5, 3, 1, 4, 2>> }
                  \* [] Len(in) = 6      -> { ... 4 solutions ... } 

TypeInv == /\ X \in InType1
           /\ cm1 \in PCR1!CtxMap
           /\ cm2 \in PCR2!CtxMap
           /\ ym  \in PCR1!ItMap
           
Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) \subseteq Solution(X) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 21:40:03 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
