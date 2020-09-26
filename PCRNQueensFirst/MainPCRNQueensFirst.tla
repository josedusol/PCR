-------------------------- MODULE MainPCRNQueensFirst ------------------------

(*
   Main module for PCR NQueensFirst.
*)

EXTENDS Typedef

LOCAL INSTANCE TLC

VARIABLES B, map   

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin (VarPType1 \union VarCType1)
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRNQueensFirst WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  map       <- map                       
           
----------------------------------------------------------------------------

vars == <<B,map>>

Init == /\ B \in InType1
        /\ PCR1!Pre(B)
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
\*        /\ PrintT("done " \o " : " \o ToString(map))          

Next == \/ \E i \in CtxIdType1 : Next1(i)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A s \in CtxIdType1 : WF_vars(Next1(s))
            
----------------------------------------------------------------------------

(* 
   Properties 
*)

Solution(in) == CASE Len(in) = 0      -> << >>
                  [] Len(in) = 1      -> <<1>>
                  [] Len(in) \in 2..3 -> << >>
                  [] Len(in) = 4      -> <<3,1,4,2>>
                  [] Len(in) = 4      -> <<2,4,1,3>>
               \* [] Len(in) = 5      -> ... 10 solutions ... 

TypeInv == /\ B \in InType1
           /\ map \in PCR1!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(B) )

Termination == <> PCR1!Finished(<<0>>)

GTermination == [][ PCR1!Finished(<<0>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Wed Sep 23 18:56:32 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
