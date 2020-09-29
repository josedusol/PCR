------------------------ MODULE MainPCRIsPrimeSeq --------------------------

(*
   Main module for PCR IsPrimeSeq.
*)

EXTENDS Typedef, FiniteSets

VARIABLES N, map1, i_p1   

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin (VarPType1 \union VarCType1)
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRIsPrimeSeq WITH
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,   
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1, 
  map       <- map1,
  i_p       <- i_p1

----------------------------------------------------------------------------

vars == <<N,map1,i_p1>>

Init == /\ N \in InType1
        /\ PCR1!Pre(N)
        /\ map1 = [i \in CtxIdType1 |-> 
                      IF   i = <<0>> 
                      THEN PCR1!InitCtx(N)
                      ELSE NULL]                  
        /\ i_p1 = PCR1!LowerBnd(N)
(* 
   PCR1 step at index I 
*)                          
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
           /\ i_p1 \in IndexType1

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(N) )
  
Termination == <> PCR1!Finished(<<0>>) 

\* This Spec is an implementation of PCRIsPrime!Spec. 
              
PCRIsPrime == INSTANCE MainPCRIsPrime 
  WITH map1 <- map1,
       i_p1 <- PCR1!LowerBnd(N)
  
=============================================================================
\* Modification History
\* Last modified Tue Sep 29 15:55:38 UYT 2020 by josedu
\* Created Sat Aug 08 21:17:14 UYT 2020 by josedu
