-------------------------- MODULE MainPCRKnapSack01 ------------------------

(*
   Main module for PCR KnapSack01.
*)

EXTENDS Typedef, Functions, FiniteSets, TLC

VARIABLES X, cm1, cm2, y    

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRKnapSack01 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1,
  cm2       <- cm2,
  y         <- y                      

PCR2 == INSTANCE PCRKnapSack01Step WITH 
  InType    <- InType2,
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,  
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  cm        <- cm2 
           
Undef == CHOOSE x : /\ x = PCR1!Undef
                    /\ x = PCR2!Undef        
           
----------------------------------------------------------------------------

vars == <<X,cm1,cm2,y>>

Init == /\ X \in InType1
        /\ PCR1!pre(X)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(X)
                     ELSE Undef]    
        /\ cm2 = [I \in CtxIdType2 |-> Undef]     
        /\ y   = Undef                                                    

(* PCR1 step at index I  *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED X    

(* PCR2 step at index I  *)                                                  
Next2(I) == /\ cm2[I] # Undef
            /\ PCR2!Next(I)
            /\ UNCHANGED <<X,cm1,y>>               

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ \A I \in PCR2!CtxIndex : PCR2!finished(I)
        /\ UNCHANGED vars         
\*        /\ PrintT("done " \o ToString(PCR1!in(<<>>)) \o " : " \o ToString(PCR1!out(<<>>)))       

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
      solSatC == { sol \in allSol  : sol.tw <= in.C }    
      solMax  == CHOOSE sol \in solSatC : \A sol2 \in solSatC : sol.tv >= sol2.tv
  IN  solMax.tv

TypeInv == /\ X \in InType1
           /\ cm1 \in PCR1!CtxMap
           /\ cm2 \in PCR2!CtxMap
           /\ y \in VarCType1 \union {Undef}
           
Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(X) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Wed Nov 04 16:48:08 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
