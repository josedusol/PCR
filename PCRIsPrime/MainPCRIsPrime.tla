------------------------- MODULE MainPCRIsPrime ----------------------------

(*
   Main module for PCR IsPrime.
*)

EXTENDS Typedef, FiniteSets, TLC

VARIABLES N, map1   

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin (Nat \union BOOLEAN)
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRIsPrime WITH
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
        /\ map1 = [i \in CtxIdType1 |-> 
                      IF   i = <<0>> 
                      THEN PCR1!InitCtx(N)
                      ELSE NULL]                  
                          
Next1(i) == /\ map1[i] # NULL
            /\ PCR1!Next(i)
            /\ UNCHANGED N              

Done == /\ \A i \in PCR1!CtxIndex : PCR1!Finished(i)
        /\ UNCHANGED vars

Next == \/ \E i \in CtxIdType1 : Next1(i)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A i \in CtxIdType1 : WF_vars(Next1(i))

----------------------------------------------------------------------------

(* 
   Properties 
*)

isPrime(n) == LET div(k,m) == \E d \in 1..m : m = k * d
              IN n > 1 /\ ~ \E m \in 2..n-1 : div(m, n)
       
Solution(n) == isPrime(n)

TypeInv == /\ N \in InType1
           /\ map1 \in PCR1!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(N) )
  
Termination == <> PCR1!Finished(<<0>>) 
  
=============================================================================
\* Modification History
\* Last modified Sat Sep 19 14:21:15 UYT 2020 by josedu
\* Created Sat Aug 08 21:17:14 UYT 2020 by josedu
