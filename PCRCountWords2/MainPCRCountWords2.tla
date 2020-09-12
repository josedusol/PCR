------------------------- MODULE MainPCRCountWords2 ------------------------

(*
   Main module for PCR CountWords2.
*)

EXTENDS Typedef, FiniteSets

VARIABLES T, W, map1, map2 

----------------------------------------------------------------------------

NULL == CHOOSE x : x \notin Nat 

\* Instanciate root PCR with appropiate types
PCR1 == INSTANCE PCRCountWords2 WITH 
  InType    <- InType1,
  LowerBnd  <- LAMBDA x : 1,
  UpperBnd  <- LAMBDA x : Len(x[1]),  
  Step      <- LAMBDA x : x+1,  
  CtxIdType <- CtxIdType1,  
  IndexType <- IndexType1,
  VarPType  <- VarPType1,
  VarCType  <- VarCType1,
  VarRType  <- VarRType1,
  map       <- map1,
  map2      <- map2

\* Instanciate auxiliary PCR with appropiate types  
PCR2 == INSTANCE PCRCountWordsInLine WITH
  InType    <- InType2,
  LowerBnd  <- LAMBDA x : 1,
  UpperBnd  <- LAMBDA x : Len(x[2]),  
  Step      <- LAMBDA x : x+1,   
  CtxIdType <- CtxIdType2,
  IndexType <- IndexType2,
  VarPType  <- VarPType2,
  VarCType  <- VarCType2,
  VarRType  <- VarRType2,  
  map       <- map2
 
----------------------------------------------------------------------------

vars == <<T,W,map1,map2>>

Init == /\ T \in TType
        /\ W \in WType
        /\ map1 = [i \in CtxIdType1 |-> 
                      IF   i = <<0>> 
                      THEN PCR1!InitCtx(<<T, W>>)
                      ELSE NULL]
        /\ map2 = [i \in CtxIdType2 |-> NULL]          
            
(* PCR1 Step *)                  
Next1(i) == /\ map1[i] # NULL
            /\ PCR1!Next(i)
            /\ UNCHANGED <<T,W>>              

(* PCR2 Step *)   
Next2(i) == /\ map2[i] # NULL
            /\ PCR2!Next(i)
            /\ UNCHANGED <<T,W,map1>>                                       

Done == /\ \A i \in PCR1!CtxIndex : PCR1!Finished(i)
        /\ \A i \in PCR2!CtxIndex : PCR2!Finished(i)
        /\ UNCHANGED vars

Next == \/ \E i \in CtxIdType1 : Next1(i)
        \/ \E i \in CtxIdType2 : Next2(i)
        \/ Done
             
Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec            
            /\ \A i \in CtxIdType1 : WF_vars(Next1(i))
            /\ \A i \in CtxIdType2 : WF_vars(Next2(i))

----------------------------------------------------------------------------

(* 
   CountWords Properties 
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
           /\ map1 \in PCR1!CtxMap
           /\ map2 \in PCR2!CtxMap

Correctness == []( PCR1!Finished(<<0>>) => PCR1!Out(<<0>>) = Solution(T,W) )

Termination == <> PCR1!Finished(<<0>>)

GTermination == [][ PCR1!Finished(<<0>>) <=> Done ]_vars


(* 
   This Spec is a more concrete implementation of PCRCountWords1!Spec. 
*)
            
subst == 
  [i \in DOMAIN map1 |-> 
      IF map1[i] # NULL
      THEN [map1[i] EXCEPT 
             !.v_p= [j \in DOMAIN @ |-> 
                       IF @[j].r = 1
                       THEN IF PCR2!Finished(i \o <<j>>)
                            THEN [v |-> @[j].v, r |-> 1]  \* when CALL_RET, producer var is marked as read.
                            ELSE [v |-> @[j].v, r |-> 0]  \* otherwise we pretend it didnt happen.
                       ELSE @[j]
                     ],
             !.v_c= [j \in DOMAIN @ |-> 
                       IF map1[i].v_p[j].r = 1 /\ PCR2!Finished(i \o <<j>>) 
                       THEN [v |-> PCR2!Out(i \o <<j>>), r |-> @[j].r]  \* when CALL_RET, the consumer var gets the result.
                       ELSE @[j]
                    ]              
           ]
      ELSE NULL]     
              
PCRCountWords1 == INSTANCE MainPCRCountWords1 WITH map <- subst

=============================================================================
\* Modification History
\* Last modified Sat Sep 12 16:06:52 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
