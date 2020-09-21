------------------------- MODULE MainPCRFibPrimes1 -------------------------

(*
   Main module for PCR FibPrimes1.
*)

EXTENDS Typedef, FiniteSets, TLC

VARIABLES N, map1   

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin (Nat \union BOOLEAN)
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRFibPrimes1 WITH 
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

(* PCR1 Step *)                  
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
                   
Fibonacci[n \in Nat] == 
  IF n < 2 
  THEN 1 
  ELSE Fibonacci[n-1] + Fibonacci[n-2]                

Solution(in) == LET fibValues == { Fibonacci[n] : n \in 0..in }
                IN  Cardinality({ f \in fibValues : isPrime(f) })

TypeInv == /\ N \in InType1
           /\ map1 \in PCR1!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(N) )
  
Termination == <> PCR1!Finished(<<0>>) 

GTermination == [][ PCR1!Finished(<<0>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Sat Sep 19 02:27:48 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
