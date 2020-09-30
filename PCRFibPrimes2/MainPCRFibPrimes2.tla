------------------------- MODULE MainPCRFibPrimes2 -------------------------

(*
   Main module for PCR FibPrimes2.
*)

EXTENDS Typedef, FiniteSets

VARIABLES N, map1, map2, i_p1, i_p2 

----------------------------------------------------------------------------

NULL == CHOOSE x : /\ x \notin (VarPType1 \union VarCType1 \union VarRType1)
                   /\ x \notin (VarPType2 \union VarCType2 \union VarRType2)

\* Instanciate first PCR with appropiate types
PCR1 == INSTANCE PCRFibPrimes2 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  map       <- map1,
  map2      <- map2,
  i_p       <- i_p1

\* Instanciate second PCR with appropiate types  
PCR2 == INSTANCE PCRIsPrime WITH
  InType    <- InType2,  
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  map       <- map2,
  i_p       <- i_p2

Undef == CHOOSE x : /\ x # PCR1!Undef
                    /\ x # PCR2!Undef
 
----------------------------------------------------------------------------

vars == <<N,map1,map2,i_p1,i_p2>>

Init == /\ N \in InType1
        /\ PCR1!Pre(N)
        /\ map1 = [I \in CtxIdType1 |-> 
                     IF   I = <<0>> 
                     THEN PCR1!InitCtx(N)
                     ELSE Undef]
        /\ map2 = [I \in CtxIdType2 |-> Undef]
        /\ i_p1 = PCR1!LowerBnd(N)
        /\ i_p2 = Undef

(* PCR1 step at index I *)                  
Next1(I) == /\ map1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED N             

(* PCR2 step at index I *)   
Next2(I) == /\ map2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<N,map1,i_p1>> 

Done == /\ \A I \in PCR1!CtxIndex : PCR1!Finished(I)
        /\ \A I \in PCR2!CtxIndex : PCR2!Finished(I)
        /\ UNCHANGED vars

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ \E I \in CtxIdType2 : Next2(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec        
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))
            /\ \A I \in CtxIdType2 : WF_vars(Next2(I))                    

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
           /\ i_p1 \in IndexType1 \union {Undef}
           /\ i_p2 \in IndexType2 \union {Undef}

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(N) )
  
Termination == <> PCR1!Finished(<<0>>) 

GTermination == [][ PCR1!Finished(<<0>>) <=> Done ]_vars

\* This Spec is an implementation of PCRFibPrimes1!Spec.
\* The following def provides a refinement mapping to prove this fact.
subst ==                        
  [I \in DOMAIN map1 |-> 
     IF map1[I] # Undef                              \* For any well-defined PCR1 context with index I
     THEN [map1[I] EXCEPT                                 
       !.v_p= [i \in DOMAIN @ |->                    \* For any producer var v_p[i]       
                 IF /\ @[i] # Undef                  \* If is written, read and C_ret(I \o <i>) 
                    /\ @[i].r > 0                    \* does not hold (PCR2 didnt finished at I \o <i>)
                    /\ ~ PCR2!Finished(I \o <<i>>)
                 THEN [v |-> @[i].v, r |-> 0]        \* then we pretend is still unread.
                 ELSE @[i]                           \* else leave it as is.
              ],
       !.v_c= [i \in DOMAIN @ |->                    \* For any consumer var v_c[i]  
                 IF /\ PCR1!Written(map1[I].v_p, i)
                    /\ PCR1!Read(map1[I].v_p, i)     \* for which corresponding v_p[i] has been read
                    /\ PCR2!Finished(I \o <<i>>)     \* and C_ret(I \o <<i>>) holds (PCR2 finished at I \o <i>)
                    /\ @[i] = Undef
                 THEN [v |-> PCR2!Out(I \o <<i>>),   \* then consumer var gets result computed by PCR2
                       r |-> 0]                    
                 ELSE @[i]                           \* else leave it as is.
              ]              
          ]
     ELSE Undef]     
              
PCRFibPrimes1 == INSTANCE MainPCRFibPrimes1 
  WITH map1 <- subst,
       i_p1 <- i_p1

=============================================================================
\* Modification History
\* Last modified Tue Sep 29 20:13:41 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
