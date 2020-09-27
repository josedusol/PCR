------------------------ MODULE MainPCRFirstEven ---------------------------

(*
   Main module for PCR FirstEven.
*)

EXTENDS Typedef, FiniteSets, TLC

VARIABLES N, map1

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin (VarPType1 \union VarCType1)
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRFirstEven WITH
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,   
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1, 
  map       <- map1

----------------------------------------------------------------------------

vars == <<N,map1>>

Init == /\ N \in InType1
        /\ PCR1!Pre(N) 
        /\ map1 = [I \in CtxIdType1 |-> 
                      IF   I = <<0>> 
                      THEN PCR1!InitCtx(N)
                      ELSE NULL]                  
                          
Next1(I) == /\ map1[I] # NULL
            /\ PCR1!Next(I)
            /\ UNCHANGED N              

Done == /\ \A I \in PCR1!CtxIndex : PCR1!Finished(I)
        /\ UNCHANGED vars
        \*        /\ PrintT("done " \o " : " \o ToString(Cardinality(DOMAIN [I \in PCR1!CtxIndex |-> map[I]] )))    
        /\ PrintT("done " \o " : " \o ToString(PCR1!Out(<<0>>)))  

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))

----------------------------------------------------------------------------

(* 
   Properties 
*)

Solution(in) == { n \in 0..in : n % 2 = 0 }

TypeInv == /\ N \in InType1
           /\ map1 \in PCR1!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) \in Solution(N) )
  
Termination == <> PCR1!Finished(<<0>>) 
  
=============================================================================
\* Modification History
\* Last modified Sun Sep 27 17:16:46 UYT 2020 by josedu
\* Created Sat Aug 08 21:17:14 UYT 2020 by josedu
