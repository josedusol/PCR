------------------------- MODULE MainPCRFibPrimes1 -------------------------

(*
   Main module for PCR FibPrimes1.
*)

EXTENDS Typedef, FiniteSets

VARIABLES N, map1, i_p1   

----------------------------------------------------------------------------

NULL == CHOOSE x : /\ x \notin (VarPType1 \union VarCType1 \union VarRType1)
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRFibPrimes1 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1, 
  map       <- map1,
  i_p       <- i_p1   
            
Undef == PCR1!Undef
            
----------------------------------------------------------------------------

vars == <<N,map1,i_p1>>

Init == /\ N \in InType1
        /\ PCR1!pre(N)
        /\ map1 = [I \in CtxIdType1 |-> 
                     IF   I = <<0>> 
                     THEN PCR1!initCtx(N)
                     ELSE Undef]
        /\ i_p1 = PCR1!lowerBnd(N)             

(* PCR1 step on index I *)                  
Next1(I) == /\ map1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED <<N>>     

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

isPrime(n) == LET div(k,m) == \E d \in 1..m : m = k * d
              IN n > 1 /\ ~ \E m \in 2..n-1 : div(m, n)
                   
fibonacci[n \in Nat] == 
  IF n < 2 
  THEN 1 
  ELSE fibonacci[n-1] + fibonacci[n-2]                

Solution(in) == LET fibValues == { fibonacci[n] : n \in 0..in }
                IN  Cardinality({ f \in fibValues : isPrime(f) })

TypeInv == /\ N \in InType1
           /\ map1 \in PCR1!CtxMap
           /\ i_p1 \in IndexType1

Correctness == []( PCR1!finished(<<0>>) => PCR1!out(<<0>>) = Solution(N) )
  
Termination == <> PCR1!finished(<<0>>) 

GTermination == [][ PCR1!finished(<<0>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Tue Sep 29 23:54:27 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
