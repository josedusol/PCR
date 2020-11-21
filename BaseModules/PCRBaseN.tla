------------------------------ MODULE PCRBaseN ------------------------------

(*
   Base module for PCR with N consumers.
*)

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE Functions

VARIABLE cm

CONSTANTS InType,       \* Type of PCR input
          CtxIdType,    \* Type of context index
          IndexType,    \* Type of iteration space
          VarPType,     \* Type of producer variable
          VarCType,     \* Types of consumer variables
          VarRType,     \* Type of reducer output
          Undef
          
\* Cartesian(<<S1,S2,...,Sn>>) = S1 \X S2 \X ... \X Sn
Cartesian(S) == 
  LET U == UNION Range(S)
      FSeq == [1..Len(S) -> U]
  IN  {s \in FSeq : \A i \in 1..Len(s) : s[i] \in S[i]}  

cLen == Len(VarCType)
          
\* Any PCR can be in exactly one of three states
State == {"OFF","RUN","END"}             

Var(T) == [IndexType -> [v : T, r : Nat] \union {Undef}]   
VarP   == Var(VarPType)
\*VarC   == VarCC(LAMBDA x : Var(x))
VarC   == Cartesian([t \in 1..cLen |-> Var(VarCType[t])])   
\*Val(T)    == [v : T, r : Nat]                                   
\*Var(D,T)  == [D -> Val(T) \union {Undef}]   
\*Vars(D,S) == Cartesian([k \in 1..Len(S) |-> Var(D,S[k])])  
         
\* Any PCR runs in a context. A context is a record with:
Ctx == [in  : InType,          \* input
        v_p : VarP,         \* producer history
        v_c : VarC,        \* consumers histories, Var(VarCType1) \X ... \X Var(VarCTypeN) 
        ret : VarRType,        \* reducer result
        ste : State]           \* discrete state     

ASSUME /\ Undef \notin Ctx
       /\ Undef \notin [v : VarPType,  r : Nat]
       /\ \A t \in 1..cLen : Undef \notin VarCType[t]

\* PCR context map. Root context is indexed at <<0>>. 
CtxMap   == [CtxIdType -> Ctx \union {Undef}] 
CtxIndex == {I \in CtxIdType : cm[I] # Undef}

\* Convenient names for context elements            
in(I)    == cm[I].in
v_p(I)   == cm[I].v_p
v_c(k,I) == cm[I].v_c[k]
out(I)   == cm[I].ret 
state(I) == cm[I].ste
in1(I)   == in(I)[1]
in2(I)   == in(I)[2] 
in3(I)   == in(I)[3]
                      
\* Useful predicates on indexes   
wellDef(I)  == cm[I] # Undef
off(I)      == cm[I].ste = "OFF"
running(I)  == cm[I].ste = "RUN"
finished(I) == cm[I].ste = "END"
   
\* Useful predicates on vars
written(var, i) == var[i] # Undef
read(var, i)    == var[i].r > 0            
             
\* Auxiliary operators over functions/records
Updf(f, x, v) == [f EXCEPT ![x] = v]
Updr(r, k, v) == [r EXCEPT !.k  = v]   
ExtR(r, s)    == [k \in DOMAIN r |-> IF k \in DOMAIN s THEN s[k] ELSE r[k]]

=============================================================================
\* Modification History
\* Last modified Fri Nov 20 23:09:53 UYT 2020 by josedu
\* Created Wed Oct 21 14:41:25 UYT 2020 by josedu
