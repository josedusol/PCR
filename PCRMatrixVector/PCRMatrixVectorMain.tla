------------------------- MODULE PCRMatrixVectorMain -----------------------

(*
   Main module for PCR MatrixVector.
*)

EXTENDS PCRMatrixVectorTypes, Functions, FiniteSets, TLC

CONSTANT Undef

VARIABLES X1, X2, X3, cm1, ym1    

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRMatrixVector WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1,
  ym        <- ym1                      
           
----------------------------------------------------------------------------

vars == <<X1,X2,X3,cm1,ym1>>

Init == /\ X1 \in In1Type1
        /\ X2 \in In2Type1
        /\ X3 \in In3Type1
        /\ PCR1!pre(<<X1,X2,X3>>)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(<<X1,X2,X3>>)
                     ELSE Undef]       
        /\ ym1 = [I \in CtxIdType1_1 |-> Undef]                                                     

(* PCR1 step at index I  *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED <<X1,X2,X3>>             

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

Sum(seq) ==
  LET F[s \in Seq(Range(seq))] ==
    IF   s = <<>> 
    THEN 0
    ELSE Head(s) + F[Tail(s)]
  IN F[seq]       
             
Solution(in1, in2, in3) == [ i \in 1..in1 |->    
                               Sum([j \in 1..in1 |-> in2[<<i,j>>] * in3[i] ]) ]

TypeInv == /\ X1 \in In1Type1
           /\ X2 \in In2Type1
           /\ X3 \in In3Type1
           /\ cm1 \in PCR1!CtxMap
           /\ ym1 \in PCR1!ItMap
           
Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(X1,X2,X3) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Tue Nov 24 23:41:11 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
