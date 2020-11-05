------------------------- MODULE MainPCRSumPrimes1 -------------------------

(*
   Main module for PCR SumPrimes1.
*)

EXTENDS Typedef, Functions, FiniteSets, TLC

VARIABLES L, cm1  

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRSumPrimes1 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  cm        <- cm1            

Undef == PCR1!Undef                    
           
----------------------------------------------------------------------------

vars == <<L,cm1>>

Init == /\ L \in InType1
        /\ PCR1!pre(L)
        /\ cm1 = [I \in CtxIdType1 |-> 
                     IF   I = <<>> 
                     THEN PCR1!initCtx(L)
                     ELSE Undef]    
                     
(* PCR1 step at index I  *)                                                  
Next1(I) == /\ cm1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED L                         

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ UNCHANGED vars         
\*        /\ PrintT("done " \o " : " \o ToString(Cardinality(DOMAIN [I \in PCR1!CtxIndex |-> map[I]] )))    
\*        /\ PrintT("done " \o ToString(PCR1!in(<<0>>)) \o " : " \o ToString(PCR1!out(<<0>>)))       

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))
            
----------------------------------------------------------------------------

(* 
   Properties 
*)

isPrime(n) == LET div(k,m) == \E d \in 1..m : m = k * d
              IN n > 1 /\ ~ \E m \in 2..n-1 : div(m, n)

Solution(in) == SeqFoldL(in, 0, LAMBDA x,y : IF isPrime(y) THEN x+y ELSE x)

TypeInv == /\ L \in InType1
           /\ cm1 \in PCR1!CtxMap

Correctness == []( PCR1!finished(<<>>) => PCR1!out(<<>>) = Solution(L) )

Termination == <> PCR1!finished(<<>>)

GTermination == [][ PCR1!finished(<<>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Thu Oct 29 16:27:04 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
