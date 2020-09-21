-------------------------- MODULE MainPCRMergeSort -------------------------

(*
   Main module for PCR MergeSort.
*)

EXTENDS Typedef, TLC

VARIABLES L, map   

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin Elem
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRMergeSort WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  map       <- map                       
           
----------------------------------------------------------------------------

vars == <<L,map>>

Init == /\ L \in InType1   
        /\ map = [i \in CtxIdType1 |-> 
                     IF   i = <<0>> 
                     THEN PCR1!InitCtx(L)
                     ELSE NULL]                            

(* PCR1 Step *)                                                  
Next1(i) == /\ map[i] # NULL
            /\ PCR1!Next(i)
            /\ UNCHANGED L    

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

Solution(in) == SortSeq(in, LAMBDA x,y : x < y)

TypeInv == /\ L \in InType1
           /\ map \in PCR1!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(L) )

Termination == <> PCR1!Finished(<<0>>)

GTermination == [][ PCR1!Finished(<<0>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Sat Sep 19 16:25:44 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
