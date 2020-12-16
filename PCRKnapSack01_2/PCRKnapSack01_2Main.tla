------------------------- MODULE PCRKnapSack01_2Main -----------------------

(*
   Main module for PCR KnapSack01_2.
   
   This is a variant of PCRKnapSack01 where we try to implement the Iterate
   PCR construct using an auxiliary PCR with sequential producer and also
   imposing some extra dependencies between consumer and reducer.
*)

EXTENDS PCRKnapSack01_2Types, Functions, FiniteSets, TLC

CONSTANT Undef

VARIABLES X, cm1, cm2, cm3

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRKnapSack01_2 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1,
  cm2       <- cm2,
  cm3       <- cm3                  

PCR2 == INSTANCE PCRKnapSack01_2Iterate WITH 
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,  
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  cm        <- cm2,
  cm3       <- cm3 

PCR3 == INSTANCE PCRKnapSack01_2Step WITH 
  InType    <- InType3,
  CtxIdType <- CtxIdType3,
  IndexType <- IndexType3,  
  VarPType  <- VarPType3,
  VarCType  <- VarCType3,
  VarRType  <- VarRType3,  
  cm        <- cm3    
           
----------------------------------------------------------------------------

vars == <<X,cm1,cm2,cm3>>

Init == /\ X \in InType1
        /\ PCR1!pre(X)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(X)
                     ELSE Undef]    
        /\ cm2 = [I \in CtxIdType2 |-> Undef]     
        /\ cm3 = [I \in CtxIdType3 |-> Undef]                                                     

(* PCR1 step at index I  *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED X    

(* PCR2 step at index I  *)                                                  
Next2(I) == /\ cm2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<X,cm1>> 
            
(* PCR2 step at index I  *)                                                  
Next3(I) == /\ cm3[I] # Undef
            /\ PCR3!Next(I)
            /\ UNCHANGED <<X,cm1,cm2>>                           

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

Sum(seq) ==
  LET f[s \in Seq(Nat)] ==
    IF   s = <<>> 
    THEN 0
    ELSE Head(s) + f[Tail(s)]
  IN f[seq]       
             
Solution(in) == 
  LET allPicks == { s \in Seq({0,1}) : Len(s) = Len(in.w) }
      allSol   == { [xs |-> x, 
                     tw |-> Sum([i \in DOMAIN x |-> in.w[i] * x[i] ]), 
                     tv |-> Sum([i \in DOMAIN x |-> in.v[i] * x[i] ])] : x \in allPicks }
      solSatC == { sol \in allSol  : sol.tw <= in.C }    
      solMax  == CHOOSE sol \in solSatC : \A sol2 \in solSatC : sol.tv >= sol2.tv
  IN  solMax.tv

TypeInv == /\ X \in InType1
           /\ cm1 \in PCR1!CtxMap
           /\ cm2 \in PCR2!CtxMap
           /\ cm3 \in PCR3!CtxMap
           
Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(X) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) <=> Done ]_vars

=============================================================================
\* Modification History
\* Last modified Wed Dec 16 15:58:58 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
