------------------------- MODULE MainPCRCountWords1 ------------------------

(*
   Main module for PCR CountWords1.
*)

EXTENDS Typedef, FiniteSets

VARIABLES T, W, map   

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin (VarPType1 \union VarCType1)
         
\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRCountWords1 WITH 
  InType    <- InType1,
  CtxIdType <- CtxIdType1,
  IndexType <- IndexType1,  
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,  
  map       <- map                       
           
----------------------------------------------------------------------------

vars == <<T,W,map>>

Init == /\ T \in TType
        /\ W \in WType       
        /\ PCR1!Pre(<<T, W>>)
        /\ map = [I \in CtxIdType1 |-> 
                     IF   I = <<0>> 
                     THEN PCR1!InitCtx(<<T, W>>)
                     ELSE NULL]                            

(* PCR1 step on index I *)                                                  
Next1(I) == /\ map[I] # NULL
            /\ PCR1!Next(I)
            /\ UNCHANGED <<T,W>>    

Done == /\ \A I \in PCR1!CtxIndex : PCR1!Finished(I)
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
           /\ map \in PCR1!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(T,W) )

Termination == <> PCR1!Finished(<<0>>)

GTermination == [][ PCR1!Finished(<<0>>) => Done ]_vars

=============================================================================
\* Modification History
\* Last modified Sat Sep 26 00:35:43 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
