------------------------ MODULE MainPCRMapFilter ---------------------------

(*
   Main module for PCR Fib.
*)

EXTENDS Typedef, FiniteSets

VARIABLES L, map1, ip1

----------------------------------------------------------------------------
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRMapFilter WITH
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,   
  VarPType  <- VarPType1,
  VarC1Type <- VarC1Type1,
  VarC2Type <- VarC2Type1,
  VarRType  <- VarRType1, 
  map       <- map1,
  ip        <- ip1

Undef == PCR1!Undef

----------------------------------------------------------------------------

vars == <<L,map1,ip1>>

Init == /\ L \in InType1
        /\ PCR1!pre(L) 
        /\ map1 = [I \in CtxIdType1 |-> 
                      IF   I = <<0>> 
                      THEN PCR1!initCtx(L)
                      ELSE Undef]  
        /\ ip1  = [I \in CtxIdType1 |-> 
                     IF   I = <<0>> 
                     THEN PCR1!lowerBnd(L)
                     ELSE Undef]                               
                          
Next1(I) == /\ map1[I] # Undef
            /\ PCR1!Next(I)
            /\ UNCHANGED L              

Done == /\ \A I \in PCR1!CtxIndex : PCR1!finished(I)
        /\ UNCHANGED vars

Next == \/ \E I \in CtxIdType1 : Next1(I)
        \/ Done
              
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A I \in CtxIdType1 : WF_vars(Next1(I))

----------------------------------------------------------------------------

(* 
   Properties 
*)


\*merge(seq1, seq2) ==
\*  LET F[s1, s2 \in Seq(Nat \union {NULL})] ==
\*        IF s1 = << >> 
\*        THEN s2 
\*        ELSE IF s2 = << >> 
\*             THEN s1 
\*             ELSE CASE Head(s1) = NULL /\ Head(s2) = NULL -> <<NULL>> \o F[Tail(s1), Tail(s2)]
\*                    [] Head(s1) # NULL /\ Head(s2) = NULL -> <<Head(s1)>> \o F[Tail(s1), Tail(s2)]
\*                    [] Head(s1) = NULL /\ Head(s2) # NULL -> <<Head(s2)>> \o F[Tail(s1), Tail(s2)]                  
\*  IN F[seq1, seq2] 

predicate(x) == x < 2      

Solution(in) == SeqFoldL(in, <<>>, LAMBDA x,y : IF predicate(y) 
                                                THEN <<y>> \o x
                                                ELSE x)    

TypeInv == /\ L \in InType1
           /\ map1 \in PCR1!CtxMap
           /\ ip1  \in PCR1!IndexMap

Correctness == []( PCR1!finished(<<0>>) => PCR1!out(<<0>>) = Solution(L) )
  
Termination == <> PCR1!finished(<<0>>) 
  
=============================================================================
\* Modification History
\* Last modified Tue Oct 13 21:03:45 UYT 2020 by josedu
\* Created Sat Aug 08 21:17:14 UYT 2020 by josedu
