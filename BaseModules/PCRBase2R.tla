----------------------------- MODULE PCRBase2R ----------------------------

(*
   Base module for PCR with two consumers.
   
   This is an experimental alternative version where the reducer is also
   a stream variable.   
*)

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

VARIABLE cm

CONSTANTS InType,        \* Type of PCR input
          CtxIdType,     \* Type of context index
          IndexType,     \* Type of iteration space
          VarPType,      \* Type of producer variable
          VarC1Type,     \* Type of consumer variable
          VarC2Type,     \* Type of consumer variable
          VarRType,      \* Type of reducer output  
          Undef       
          
\* Any PCR can be in exactly one of three states
State == {"OFF","RUN","END"}                         
             
\* A variable is a mapping from assignments to values
Var(T) == [IndexType -> [v : T, r : Nat] \union {Undef}]
  
VarP  == Var(VarPType)
VarC1 == Var(VarC1Type)
VarC2 == Var(VarC2Type)
VarR  == Var(VarRType)  
                 
\* Any PCR runs in a context. A context is a record with:
Ctx == [in   : InType,          \* input
        v_p  : VarP,            \* producer history
        v_c1 : VarC1,           \* consumer 1 history
        v_c2 : VarC2,           \* consumer 2 history
        v_r  : VarR,            \* reducer history
        i_r  : IndexType,       \* reducer index
        ste  : State]           \* discrete state   

ASSUME /\ Undef \notin Ctx
       /\ Undef \notin [v : VarPType,  r : Nat]
       /\ Undef \notin [v : VarC1Type, r : Nat]
       /\ Undef \notin [v : VarC2Type, r : Nat]
       /\ Undef \notin [v : VarRType,  r : Nat]

\* PCR context map. Root context is indexed at <<0>>. 
CtxMap   == [CtxIdType -> Ctx \union {Undef}] 
CtxIndex == {I \in CtxIdType : cm[I] # Undef}

\* Convenient names for context elements            
in(I)    == cm[I].in
v_p(I)   == cm[I].v_p
v_c1(I)  == cm[I].v_c1
v_c2(I)  == cm[I].v_c2
v_r(I)   == cm[I].v_r
i_r(I)   == cm[I].i_r
out(I)   == cm[I].v_r[cm[I].i_r].v
state(I) == cm[I].ste
in1(I)   == in(I)[1]
in2(I)   == in(I)[2] 
in3(I)   == in(I)[3]
                      
\* Useful predicates on indexes   
wellDef(I)    == cm[I] # Undef
off(I)        == cm[I].ste = "OFF"
running(I)    == cm[I].ste = "RUN"
finished(I)   == cm[I].ste = "END"
pending(I, i) == cm[I].v_r[i].r = 0
   
\* Useful predicates on vars
written(var, i) == var[i] # Undef
read(var, i)    == var[i].r > 0
             
\* Auxiliary operators over functions/records
Updf(f, x, v) == [f EXCEPT ![x] = v]
Updr(r, k, v) == [r EXCEPT !.k  = v]   
ExtR(r, s)    == [k \in DOMAIN r |-> IF k \in DOMAIN s THEN s[k] ELSE r[k]]
               
=============================================================================
\* Modification History
\* Last modified Sat Nov 21 16:50:29 UYT 2020 by josedu
\* Last modified Mon Jul 06 15:51:49 UYT 2020 by josed
\* Last modified Tue Jun 09 12:24:42 GMT-03:00 2020 by JosEdu
\* Created Mon Jun 08 22:50:44 GMT-03:00 2020 by JosEdu
