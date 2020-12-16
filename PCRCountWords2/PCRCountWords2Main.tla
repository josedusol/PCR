------------------------- MODULE PCRCountWords2Main ------------------------

(*
   Main module for PCR CountWords2.
*)

EXTENDS PCRCountWords2Types, FiniteSets, TLC

CONSTANT Undef

VARIABLES T, W, cm1, cm2

----------------------------------------------------------------------------

\* Instanciate first PCR with appropiate types
PCR1 == INSTANCE PCRCountWords2 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,  
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,
  cm        <- cm1,
  cm2       <- cm2

\* Instanciate second PCR with appropiate types  
PCR2 == INSTANCE PCRCountWordsInLine WITH
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  cm        <- cm2
 
----------------------------------------------------------------------------

vars == <<T,W,cm1,cm2>>

Init == /\ T \in TType
        /\ W \in WType
        /\ PCR1!pre(<<T, W>>)
        /\ cm1 = [I \in CtxIdType1 |-> 
                      IF   I = <<>> 
                      THEN PCR1!initCtx(<<T, W>>)
                      ELSE Undef]           
        /\ cm2 = [I \in CtxIdType2 |-> Undef]           
            
(* PCR1 step on index I *)                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED <<T,W>>              

(* PCR2 step on index I *)   
Next2(I) == /\ cm2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<T,W,cm1>>                                       

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

count(line, w) ==
  IF   w \in Range(line) 
  THEN [w2 \in {w} |-> Cardinality({n \in DOMAIN line : line[n] = w2})]
  ELSE EmptyBag   

Solution(in1, in2) == 
  Fold(Flatten([l \in DOMAIN in1 |-> 
                     [w \in DOMAIN in2 |-> 
                           count(in1[l], in2[w])]]),
       EmptyBag,
       LAMBDA x,y : x (+) y)

TypeInv == /\ T \in TType
           /\ W \in WType
           /\ cm1 \in PCR1!CtxMap
           /\ cm2 \in PCR2!CtxMap 

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(T,W) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) <=> Done ]_vars

\* This Spec is an implementation of PCRCountWords1!Spec.
\* The following def provides a refinement mapping to prove this fact.
subst ==                        
  [I \in DOMAIN cm1 |-> 
     IF cm1[I] # Undef                               \* For any well-defined PCR1 context with index I
     THEN [cm1[I] EXCEPT                                 
       !.v_p= [i \in DOMAIN @ |->                    \* For any producer var v_p[i]       
                 IF /\ @[i] # Undef                  \* If is written, read and C_ret(I \o <i>) 
               \*   /\ @[i].r > 0                    \* does not hold (PCR2 didnt finished at I \o <i>)
                    /\ PCR2!wellDef(I \o <<i>>)
                    /\ ~ PCR2!finished(I \o <<i>>)
                 THEN [v |-> @[i].v, r |-> 0]        \* then we pretend is still unread.
                 ELSE @[i]                           \* else leave it as is.
              ],
       !.v_c= [i \in DOMAIN @ |->                    \* For any consumer var v_c[i]  
                 IF /\ @[i] = Undef
                    /\ PCR1!written(cm1[I].v_p, i)
               \*    /\ PCR1!read(cm1[I].v_p, i)      \* for which corresponding v_p[i] has been read
                    /\ PCR2!wellDef(I \o <<i>>)
                    /\ PCR2!finished(I \o <<i>>)     \* and C_ret(I \o <<i>>) holds (PCR2 finished at I \o <i>)                   
                 THEN [v |-> PCR2!out(I \o <<i>>),   \* then consumer var gets result computed by PCR2
                       r |-> 0]                    
                 ELSE @[i]                           \* else leave it as is.
              ]              
          ]
     ELSE Undef] 
              
PCRCountWords1 == INSTANCE PCRCountWords1Main
  WITH cm1 <- subst

=============================================================================
\* Modification History
\* Last modified Sun Dec 13 14:34:25 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
