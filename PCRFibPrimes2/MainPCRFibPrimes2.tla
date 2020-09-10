------------------------- MODULE MainPCRFibPrimes2 -------------------------

(*
   Main module for PCR FibPrimes2.
*)

EXTENDS Typedef, FiniteSets, TLC, TLAPS, Functions

VARIABLES N, map1, map2 

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin (Nat \union BOOLEAN) 

\* Instanciate first PCR with appropiate types
PCR1 == INSTANCE PCRFibPrimes2 WITH 
  InType    <- InType1,
  LowerBnd  <- LAMBDA x : 0,
  UpperBnd  <- LAMBDA x : x,  
  Step      <- LAMBDA x : x + 1,
  IndexType <- IndexType1,
  CtxIdType <- CtxIdType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  map       <- map1,
  map2      <- map2

\* Instanciate second PCR with appropiate types  
PCR2 == INSTANCE PCRIsPrime WITH
  InType    <- InType2,  
  LowerBnd  <- LAMBDA x : 2,
  UpperBnd  <- LAMBDA x : Sqrt(x),  
  Step      <- LAMBDA x : 2*x - 1,
  IndexType <- IndexType2,
  CtxIdType <- CtxIdType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  map       <- map2 
 
----------------------------------------------------------------------------

vars == <<N,map1,map2>>

Init == /\ N \in InType1
        /\ map1 = [i \in CtxIdType1 |-> 
                     IF   i = <<0>> 
                     THEN PCR1!InitCtx(N)
                     ELSE NULL]
        /\ map2 = [i \in CtxIdType2 |-> NULL]

(* PCR1 Step *)                  
Next1(i) == /\ map1[i] # NULL
            /\ PCR1!Next(i)
            /\ UNCHANGED N             

(* PCR2 Step *)   
Next2(i) == /\ map2[i] # NULL
            /\ PCR2!Next(i)
            /\ UNCHANGED <<N,map1>> 

Done == /\ \A i \in PCR1!CtxIndex : PCR1!Finished(i)
        /\ \A i \in PCR2!CtxIndex : PCR2!Finished(i)
        /\ UNCHANGED vars

Next == \/ \E i \in CtxIdType1 : Next1(i)
        \/ \E i \in CtxIdType2 : Next2(i)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec        
            /\ \A i \in CtxIdType1 : WF_vars(Next1(i))
            /\ \A i \in CtxIdType2 : WF_vars(Next2(i))                    

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
           /\ map2 \in PCR2!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(N) )
  
Termination == <> PCR1!Finished(<<0>>) 

GTermination == [][ PCR1!Finished(<<0>>) <=> Done ]_vars

(* 
   This Spec is a more concrete implementation of Boot1!Spec. 
*)
            
subst ==                        
  [i \in DOMAIN map1 |-> 
      IF map1[i] # NULL
      THEN [map1[i] EXCEPT 
              !.v_p= [j \in DOMAIN @ |-> 
                         IF @[j].r = 1
                         THEN IF PCR2!Finished(i \o <<j>>) 
                              THEN [v |-> @[j].v, r |-> 1]  \* when CALL_RET, producer var is marked as read.
                              ELSE [v |-> @[j].v, r |-> 0]  \* otherwise we pretend it didnt happen.
                         ELSE @[j]
                      ],
              !.v_c= [j \in DOMAIN @ |-> 
                         IF map1[i].v_p[j].r = 1 /\ PCR2!Finished(i \o <<j>>) 
                         THEN [v |-> PCR2!Out(i \o <<j>>), r |-> @[j].r]  \* when CALL_RET, the consumer var gets the result.
                         ELSE @[j]
                     ]              
            ]
      ELSE NULL]     
              
PCRFibPrimes1 == INSTANCE MainPCRFibPrimes1 WITH map1 <- subst

=============================================================================
\* Modification History
\* Last modified Wed Sep 09 20:09:21 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
