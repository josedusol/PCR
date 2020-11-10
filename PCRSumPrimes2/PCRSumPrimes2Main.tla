------------------------- MODULE PCRSumPrimes2Main -------------------------

(*
   Main module for PCR SumPrimes2.
*)

EXTENDS PCRSumPrimes2Types, Functions, FiniteSets, TLC

CONSTANT Undef

VARIABLES L, cm1, cm2   

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRSumPrimes2 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1,
  cm2       <- cm2             
           
\* Instanciate second PCR with appropiate types  
PCR2 == INSTANCE PCRIsPrime WITH
  InType    <- InType2,  
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,
  cm        <- cm2                    
           
----------------------------------------------------------------------------

vars == <<L,cm1,cm2>>

Init == /\ L \in InType1
        /\ PCR1!pre(L)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(L)
                     ELSE Undef]    
        /\ cm2 = [I \in CtxIdType2 |-> Undef]                                                  

(* PCR1 step at index I  *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED L 
            
(* PCR2 step at index I  *)                                                  
Next2(I) == /\ cm2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<L,cm1>>               

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ \A I \in PCR2!CtxIndex : PCR2!finished(I)
        /\ UNCHANGED vars         
\*        /\ PrintT("Done: In = " \o ToString(PCR1!in(<<>>))
\*                 \o " - Out = " \o ToString(PCR1!out(<<>>)))

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

Solution(in) == SeqFoldL(in, 0, LAMBDA x,y : IF isPrime(y) THEN x+y ELSE x)

TypeInv == /\ L \in InType1
           /\ cm1 \in PCR1!CtxMap
           /\ cm2 \in PCR2!CtxMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(L) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) => Done ]_vars

\* This Spec is an implementation of PCRSumPrimes1!Spec.
\* The following def provides a refinement mapping to prove this fact.
subst ==                        
  [I \in DOMAIN cm1 |-> 
     IF cm1[I] # Undef                               \* For any well-defined PCR1 context with index I
     THEN [cm1[I] EXCEPT                                 
       !.v_p= [i \in DOMAIN @ |->                    \* For any producer var v_p[i]       
                 IF /\ @[i] # Undef                  \* If is written, read and C_ret(I \o <i>) 
                    /\ @[i].r > 0                    \* does not hold (PCR2 didnt finished at I \o <i>)
                    /\ ~ PCR2!finished(I \o <<i>>)
                 THEN [v |-> @[i].v, r |-> 0]        \* then we pretend is still unread.
                 ELSE @[i]                           \* else leave it as is.
              ],
       !.v_c= [i \in DOMAIN @ |->                                \* For any consumer var v_c[i]  
                 IF /\ @[i] = Undef
                    /\ PCR1!written(cm1[I].v_p, i)
                    /\ PCR1!read(cm1[I].v_p, i)                  \* for which corresponding v_p[i] has been read
                    /\ PCR1!isBase(PCR1!in(I), PCR1!v_p(I), i)
                    /\ PCR1!v_p(I)[i].v # << >>
                    /\ PCR2!finished(I \o <<i>>)                 \* and C_ret(I \o <<i>>) holds (PCR2 finished at I \o <i>)                                      
                 THEN IF PCR2!out(I \o <<i>>)
                      THEN [v |-> (PCR1!v_p(I)[i].v)[1],         \* then consumer var gets result computed by PCR2
                            r |-> 0]
                      ELSE [v |-> 0,                       
                            r |-> 0]                                         
                 ELSE @[i]                           \* else leave it as is.
              ]              
          ]
     ELSE Undef]     
              
PCRSumPrimes1 == INSTANCE PCRSumPrimes1Main 
  WITH cm1 <- subst
       
=============================================================================
\* Modification History
\* Last modified Mon Nov 09 21:40:50 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
