------------------------- MODULE PCRKnapSack01_4Main -----------------------

(*
   Main module for PCR KnapSack01_4.
*)

EXTENDS PCRKnapSack01_4Types, Functions, FiniteSets, TLC

CONSTANT Undef

VARIABLES X, cm1, cm2, ym1    

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRKnapSack01_4 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarC1Type <- VarC1Type1,
  VarC2Type <- VarC2Type1,
  VarRType  <- VarRType1,  
  cm        <- cm1,
  cm2       <- cm2,
  ym        <- ym1                      

PCR2 == INSTANCE PCRKnapSack01_4Step WITH 
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,  
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  cm        <- cm2    
           
----------------------------------------------------------------------------

vars == <<X,cm1,cm2,ym1>>

Init == /\ X \in InType1
        /\ PCR1!pre(X)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(X)
                     ELSE Undef]    
        /\ cm2 = [I \in CtxIdType2 |-> Undef]     
        /\ ym1 = [I \in CtxIdType1_1 |-> Undef]                                                     

(* PCR1 step at index I  *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED X    

(* PCR2 step at index I  *)                                                  
Next2(I) == /\ cm2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<X,cm1,ym1>>               

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

Sum(seq) ==
  LET F[s \in Seq(Nat)] ==
    IF   s = <<>> 
    THEN 0
    ELSE Head(s) + F[Tail(s)]
  IN F[seq]       
             
Solution(in) == 
  LET allPicks == { s \in Seq({0,1}) : Len(s) = Len(in.w) }
      allSol   == { [xs |-> x, 
                     tw |-> Sum([i \in DOMAIN x |-> in.w[i] * x[i] ]), 
                     tv |-> Sum([i \in DOMAIN x |-> in.v[i] * x[i] ])] : x \in allPicks }
      solSatC  == { s \in allSol  : s.tw <= in.C }    
      solMax   == { s \in solSatC : \A s2 \in solSatC : s.tv >= s2.tv }
  IN  { [items |-> s.xs, profit |-> s.tv] : s \in solMax }  

TypeInv == /\ X \in InType1
           /\ cm1 \in PCR1!CtxMap
           /\ cm2 \in PCR2!CtxMap
           /\ ym1 \in PCR1!ItMap
           
Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) \in Solution(X) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) <=> Done ]_vars

=============================================================================
\* Modification History
\* Last modified Wed Nov 25 16:23:33 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
