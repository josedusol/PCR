------------------------- MODULE PCRFibPrimes4Main -------------------------

(*
   Main module for PCR FibPrimes4.
*)

EXTENDS PCRFibPrimes4Types, FiniteSets

CONSTANT Undef

VARIABLES N, cm1, cm2, im1

----------------------------------------------------------------------------                  

\* Instanciate first PCR with appropiate types
PCR1 == INSTANCE PCRFibPrimes4 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1,
  cm2       <- cm2,
  im        <- im1

\* Instanciate second PCR with appropiate types  
PCR2 == INSTANCE PCRFibRec WITH
  InType    <- InType2,  
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  cm       <- cm2
 
----------------------------------------------------------------------------

vars == <<N,cm1,cm2,im1>>

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

(* PCR1 step at index I *)                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED N             

(* PCR2 step at index I *)   
Next2(I) == /\ cm2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<N,cm1,im1>> 

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ \A I \in PCR2!CtxIndex : PCR2!finished(I)
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
       
fibonacci[n \in Nat] == 
  IF n < 2 
  THEN 1 
  ELSE fibonacci[n-1] + fibonacci[n-2]                

Solution(in) == LET fibValues == { fibonacci[n] : n \in 0..in }
                IN  Cardinality({ f \in fibValues : isPrime(f) })

TypeInv == /\ N \in InType1
           /\ cm1 \in PCR1!CtxMap
           /\ cm2 \in PCR2!CtxMap
           /\ im1 \in PCR1!IndexMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(N) )
  
Termination == <> PCR1!finished(<<>>) 

GTermination == [][ PCR1!finished(<<>>) <=> Done ]_vars

\* This Spec is an implementation of PCRFibPrimes1!Spec.
\* The following def provides a refinement mapping to prove this fact.
subst ==                        
  [I \in DOMAIN cm1 |-> 
     IF cm1[I] # Undef                              \* For any well-defined PCR1 context with index I
     THEN [cm1[I] EXCEPT          
       !.v_p= [i \in DOMAIN @ |->          
                 IF /\ @[i] # Undef                 \* For any non-read producer var v_p[i]
\*                    /\ @[i].r = 0                   \* for which P_ret(I \o <i>) holds (PCR2 finished at I \o <i>)                   
                    /\ PCR2!wellDef(I \o <<i>>)
                    /\ PCR2!finished(I \o <<i>>)       
                 THEN [v |-> PCR2!out(I \o <<i>>),  \* then producer var gets result computed by PCR2
                       r |-> @[i].r]                        
                 ELSE @[i]                          \* else leave it as is.                     
              ]                                     
          ]
     ELSE Undef]      
              
PCRFibPrimes1 == INSTANCE PCRFibPrimes1Main 
  WITH cm1 <- subst,
       im1 <- im1

=============================================================================
\* Modification History
\* Last modified Mon Dec 14 19:52:43 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
