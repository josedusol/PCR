----------------------- MODULE MainPCRCountWordsInLine ----------------------

(*
   Main module for PCR CountWordsInLine.
*)

EXTENDS Typedef, FiniteSets

VARIABLES L, W, cm1

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRCountWordsInLine WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,
  cm        <- cm1                

Undef == PCR1!Undef
           
----------------------------------------------------------------------------

vars == <<L,W,cm1>>

Init == /\ L \in LType
        /\ W \in WType       
        /\ PCR1!pre(<<L, W>>)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(<<L, W>>)
                     ELSE Undef]
                     
(* PCR1 step at index I *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED <<L,W>>    

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ UNCHANGED vars                 

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))
            
----------------------------------------------------------------------------

(* 
   Properties 
*)

count(line, w) ==
  IF   w \in Range(line) 
  THEN [w2 \in {w} |-> Cardinality({n \in DOMAIN line : line[n] = w2})]
  ELSE EmptyBag   

Solution(in1, in2) == 
  Fold([w \in DOMAIN in2 |-> count(in1, in2[w])],
       EmptyBag,
       LAMBDA x,y : x (+) y)
      
TypeInv == /\ L \in LType
           /\ W \in WType
           /\ cm1 \in PCR1!CtxMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(L,W) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 22:55:43 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
