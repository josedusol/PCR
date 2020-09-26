------------------------- MODULE MainPCRFibPrimes6 -------------------------

(*
   Main module for PCR FibPrimes6.
*)

EXTENDS Typedef, FiniteSets

VARIABLES N, map1, map2, map3 

----------------------------------------------------------------------------

NULL == CHOOSE x : /\ x \notin (VarPType1 \union VarCType1)
                   /\ x \notin (VarPType2 \union VarCType2)
                   /\ x \notin (VarPType3 \union VarCType3)

\* Instanciate first PCR with appropiate types
PCR1 == INSTANCE PCRFibPrimes6 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  map       <- map1,
  map2      <- map2,
  map3      <- map3

\* Instanciate second PCR with appropiate types  
PCR2 == INSTANCE PCRFib WITH
  InType    <- InType2,  
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  map       <- map2 
  
PCR3 == INSTANCE PCRIsPrime WITH
  InType    <- InType3,
  CtxIdType <- CtxIdType3,
  IndexType <- IndexType3,
  VarPType  <- VarPType3,
  VarCType  <- VarCType3,
  VarRType  <- VarRType3,
  map       <- map3  
 
----------------------------------------------------------------------------

vars == <<N,map1,map2,map3>>

Init == /\ N \in InType1
        /\ PCR1!Pre(N)
        /\ map1 = [i \in CtxIdType1 |-> 
                     IF   i = <<0>> 
                     THEN PCR1!InitCtx(N)
                     ELSE NULL]
        /\ map2 = [i \in CtxIdType2 |-> NULL]
        /\ map3 = [i \in CtxIdType3 |-> NULL]

(* PCR1 Step *)                  
Next1(i) == /\ map1[i] # NULL
            /\ PCR1!Next(i)
            /\ UNCHANGED N             

(* PCR2 Step *)   
Next2(i) == /\ map2[i] # NULL
            /\ PCR2!Next(i)
            /\ UNCHANGED <<N,map1,map3>> 
            
(* PCR3 Step *)   
Next3(i) == /\ map3[i] # NULL
            /\ PCR3!Next(i)
            /\ UNCHANGED <<N,map1,map2>>             

Done == /\ \A i \in PCR1!CtxIndex : PCR1!Finished(i)
        /\ \A i \in PCR2!CtxIndex : PCR2!Finished(i)
        /\ \A i \in PCR3!CtxIndex : PCR3!Finished(i)
        /\ UNCHANGED vars

Next == \/ \E i \in CtxIdType1 : Next1(i)
        \/ \E i \in CtxIdType2 : Next2(i)
        \/ \E i \in CtxIdType3 : Next3(i)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec        
            /\ \A i \in CtxIdType1 : WF_vars(Next1(i))
            /\ \A i \in CtxIdType2 : WF_vars(Next2(i))       
            /\ \A i \in CtxIdType3 : WF_vars(Next3(i))             

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
           /\ map3 \in PCR3!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(N) )
  
Termination == <> PCR1!Finished(<<0>>) 

GTermination == [][ PCR1!Finished(<<0>>) <=> Done ]_vars

\* This Spec is an implementation of PCRFibPrimes1!Spec.
\* The following def provides a refinement mapping to prove this fact.
subst ==                        
  [i \in DOMAIN map1 |-> 
     IF map1[i] # NULL                                   \* For any well-defined PCR1 context with index i
     THEN [map1[i] EXCEPT                                 
       !.v_p= [j \in DOMAIN @ |->                        \* For any producer var v_p[j]
                 IF @[j].r > 0                           \* If has been read
                 THEN IF PCR3!Finished(i \o <<j>>)       \*   and C_ret(i \o <j>) holds (PCR2 finished at i\o<j>)
                      THEN [v |-> @[j].v, r |-> 1]       \*   then producer var is marked as read
                      ELSE [v |-> @[j].v, r |-> 0]       \*   else we pretend is still unread.
                 ELSE IF /\ @[j].v # NULL                \* else if is non-null
                         /\ PCR2!Finished(i \o <<j>>)    \*   is non-null and P_ret(i \o <<j>>) holds (PCR2 finished at i\o<j>)
                      THEN [v |-> PCR2!Out(i \o <<j>>),  \*   then producer var gets result computed by PCR2
                            r |-> 0]                        
                      ELSE @[j]                          \* otherwise leave it as is.    
              ],
       !.v_c= [j \in DOMAIN @ |->                        \* For any consumer var v_c[j]
                 IF /\ PCR1!Read(map1[i].v_p, j)         \* for which corresponding v_p[j] has been read
                    /\ PCR3!Finished(i \o <<j>>)         \* and C_ret(i \o <<j>>) holds (PCR2 finished at i\o<j>)
                 THEN [v |-> PCR3!Out(i \o <<j>>),       \* then consumer var gets result computed by PCR2
                       r |-> @[j].r]                 
                 ELSE @[j]                               \* else leave it as is.
              ]              
          ]
     ELSE NULL]     
              
PCRFibPrimes1 == INSTANCE MainPCRFibPrimes1 WITH map1 <- subst

=============================================================================
\* Modification History
\* Last modified Fri Sep 25 23:34:43 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
