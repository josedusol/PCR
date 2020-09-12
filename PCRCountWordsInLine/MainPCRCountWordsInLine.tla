----------------------- MODULE MainPCRCountWordsInLine ----------------------

(*
   Main module for PCR CountWordsInLine.
*)

EXTENDS Typedef, FiniteSets, TLC, TLAPS, Functions

VARIABLES L, W, map   

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin Nat
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRCountWordsInLine WITH 
  InType    <- InType1,
  LowerBnd  <- LAMBDA x : 1,
  UpperBnd  <- LAMBDA x : Len(x[2]),  
  Step      <- LAMBDA x : x+1,   
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,
  map       <- map                  
           
----------------------------------------------------------------------------

vars == <<L,W,map>>

Init == /\ L \in LType
        /\ W \in WType       
        /\ map = [i \in CtxIdType1 |-> 
                     IF   i = <<0>> 
                     THEN PCR1!InitCtx(<<L, W>>)
                     ELSE NULL]                            

(* PCR1 Step *)                                                  
Next1(i) == /\ map[i] # NULL
            /\ PCR1!Next(i)
            /\ UNCHANGED <<L,W>>    

Done == /\ \A i \in PCR1!CtxIndex : PCR1!Finished(i)
        /\ UNCHANGED vars                 

Next == \/ \E i \in CtxIdType1 : Next1(i)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A s \in CtxIdType1 : WF_vars(Next1(s))
            
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
           /\ map \in PCR1!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(L,W) )

Termination == <> PCR1!Finished(<<0>>)

GTermination == [][ PCR1!Finished(<<0>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Sat Sep 12 17:46:00 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
