------------------------- MODULE PCRFibPrimes6Main -------------------------

(*
   Main module for PCR FibPrimes6.
*)

EXTENDS PCRFibPrimes6Types, FiniteSets, TLC

CONSTANT Undef

VARIABLES N, cm1, cm2, cm3, im1, im2

----------------------------------------------------------------------------
                                     
\* Instanciate first PCR with appropiate types
PCR1 == INSTANCE PCRFibPrimes6 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1,
  cm2       <- cm2,
  cm3       <- cm3,
  im        <- im1,
  im2       <- im2

\* Instanciate second PCR with appropiate types  
PCR2 == INSTANCE PCRFib WITH
  InType    <- InType2,  
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  cm        <- cm2,
  im        <- im2

\* Instanciate third PCR with appropiate types   
PCR3 == INSTANCE PCRIsPrime WITH
  InType    <- InType3,
  CtxIdType <- CtxIdType3,
  IndexType <- IndexType3,
  VarPType  <- VarPType3,
  VarCType  <- VarCType3,
  VarRType  <- VarRType3,
  cm        <- cm3
 
----------------------------------------------------------------------------

vars == <<N,cm1,cm2,cm3,im1,im2>>

Init == /\ N \in InType1
        /\ PCR1!pre(N)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(N)
                     ELSE Undef]
        /\ im1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!lowerBnd(N)
                     ELSE Undef] 
        /\ cm2 = [I \in CtxIdType2 |-> Undef]            
        /\ im2 = [I \in CtxIdType2 |-> Undef]
        /\ cm3 = [I \in CtxIdType3 |-> Undef]

(* PCR1 step at index I *)              
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED N             

(* PCR2 step at index I *) 
Next2(I) == /\ cm2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<N,cm1,cm3,im1>> 
            
(* PCR3 step at index I *)
Next3(I) == /\ cm3[I] # Undef
            /\ PCR3!Next(I)
            /\ UNCHANGED <<N,cm1,cm2,im1,im2>>             

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ \A I \in PCR2!CtxIndex : PCR2!finished(I)
        /\ \A I \in PCR3!CtxIndex : PCR3!finished(I)
        /\ UNCHANGED vars
\*        /\ PrintT("Done: In = " \o ToString(PCR1!in(<<>>))
\*                 \o " - Out = " \o ToString(PCR1!out(<<>>)))

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ \E I \in CtxIdType2 : Next2(I)
        \/ \E I \in CtxIdType3 : Next3(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec        
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))
            /\ \A I \in CtxIdType2 : WF_vars(Next2(I))       
            /\ \A I \in CtxIdType3 : WF_vars(Next3(I))             

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
           /\ cm1 \in PCR1!CtxMap
           /\ cm2 \in PCR2!CtxMap
           /\ cm3 \in PCR3!CtxMap
           /\ im1 \in PCR1!IndexMap
           /\ im2 \in PCR2!IndexMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(N) )
  
Termination == <> PCR1!finished(<<>>) 

GTermination == [][ PCR1!finished(<<>>) <=> Done ]_vars

\* This Spec is an implementation of PCRFibPrimes1!Spec.
\* The following def provides a refinement mapping to prove this fact.
subst ==                        
  [I \in DOMAIN cm1 |-> 
     IF cm1[I] # Undef                                    \* For any well-defined PCR1 context with index I
     THEN [cm1[I] EXCEPT                                 
       !.v_p= [i \in DOMAIN @ |->                         \* For any producer var v_p[i]
                 IF /\ @[i] # Undef
                    /\ ~ PCR3!wellDef(I \o <<i>>)
                 THEN IF /\ PCR2!wellDef(I \o <<i>>)      \*   and C_ret(I \o <i>) holds (PCR2 finished at I\o<i>)
                         /\ PCR2!finished(I \o <<i>>)
                      THEN [v |-> PCR2!out(I \o <<i>>),   \*   then producer var gets result computed by PCR2
                            r |-> @[i].r]                        
                      ELSE @[i]
                 ELSE IF /\ @[i] # Undef            
                         /\ ~ PCR3!finished(I \o <<i>>)
                      THEN [v |-> @[i].v, r |-> 0]        \*   else leave it as is.
                      ELSE @[i]                                                  
              ], 
       !.v_c= [i \in DOMAIN @ |->                         \* For any consumer var v_c[i]
                 IF /\ @[i] = Undef                       \* for which corresponding v_p[i] has been written and read
                    /\ PCR1!written(cm1[I].v_p, i)        \* and C_ret(I \o <i>) holds (PCR2 finished at I \o <i>)
\*                    /\ PCR1!read(cm1[I].v_p, i)         
                    /\ PCR3!wellDef(I \o <<i>>)
                    /\ PCR3!finished(I \o <<i>>)         
                 THEN [v |-> PCR3!out(I \o <<i>>),        \* then consumer var gets result computed by PCR3
                       r |-> 0]                 
                 ELSE @[i]                                \* else leave it as is.
              ]              
          ]
     ELSE Undef]     
              
PCRFibPrimes1 == INSTANCE PCRFibPrimes1Main 
  WITH cm1 <- subst,
       im1 <- im1

=============================================================================
\* Modification History
\* Last modified Mon Dec 14 22:18:51 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
