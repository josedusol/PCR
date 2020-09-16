-------------------------- MODULE MainPCRNQueensAll ------------------------

(*
   Main module for PCR NQueensAll.
*)

EXTENDS Typedef, FiniteSets, TLC

VARIABLES B, map   

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin (Nat \union BOOLEAN)
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRNQueensAll WITH 
  InType    <- InType1,
  LowerBnd  <- LAMBDA x : 1,
  UpperBnd  <- LAMBDA x : Len(x.sol),  
  Step      <- LAMBDA x : x + 1,  
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  map       <- map                       
           
----------------------------------------------------------------------------

vars == <<B,map>>

Init == /\ B \in InType1   
        /\ B.sol = [i \in Size\{0} |-> 0]
        /\ B.i   = 1
        /\ B.j   = 1
        /\ map = [i \in CtxIdType1 |-> 
                     IF   i = <<0>> 
                     THEN PCR1!InitCtx(B)
                     ELSE NULL]                            

(* PCR1 Step *)                                                  
Next1(i) == /\ map[i] # NULL
            /\ PCR1!Next(i)
            /\ UNCHANGED B    

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

Solution(in) == CASE Len(in.sol) < 4 -> { }
                  [] Len(in.sol) = 4 -> { <<3,1,4,2>>, <<2,4,1,3>> }
               \* [] Len(in.sol) = 5 -> { ... 10 solutions ... }

TypeInv == /\ B \in InType1
           /\ map \in PCR1!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(B) )

Termination == <> PCR1!Finished(<<0>>)

GTermination == [][ PCR1!Finished(<<0>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Wed Sep 16 17:46:50 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
