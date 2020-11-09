----------------------------- MODULE PCRBaseG -----------------------------

(*
   Base module for any PCR.
*)

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

VARIABLE cm

CONSTANTS InType,       \* Type of PCR input
          CtxIdType,    \* Type of context index
          IndexType,    \* Type of iteration space
          VarPType,     \* Type of producer variable
          VarCType,     \* Type of consumer variable
          VarRType,     \* Type of reducer output
          Undef
          
\* Any PCR can be in exactly one of three states
State == {"OFF","RUN","END"}                      
                 
VarP == [IndexType -> [v : VarPType, r : Nat] \union {Undef}]
VarC == [IndexType -> [v : VarCType, r : Nat] \union {Undef}]                

\* Any PCR runs in a context. A context is a record with:
Ctx == [in  : InType,       \* input
        v_p : VarP,         \* producer history
        v_c : VarC,         \* consumer history
        ret : VarRType,     \* reducer result
        ste : State]        \* discrete state     

ASSUME /\ Undef \notin Ctx
       /\ [v : VarPType, r : Nat]
       /\ [v : VarCType, r : Nat]

\* PCR context map. Root context is indexed at <<0>>. 
CtxMap   == [CtxIdType -> Ctx \union {Undef}] 
CtxIndex == {I \in CtxIdType : cm[I] # Undef}

\* Convenient names for context elements            
in(I)    == cm[I].in
v_p(I)   == cm[I].v_p
v_c(I)   == cm[I].v_c
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
\* Last modified Fri Nov 06 14:41:34 UYT 2020 by josedu
\* Last modified Mon Jul 06 15:51:49 UYT 2020 by josed
\* Last modified Tue Jun 09 12:24:42 GMT-03:00 2020 by JosEdu
\* Created Mon Jun 08 22:50:44 GMT-03:00 2020 by JosEdu
