----------------------------- MODULE PCRBase ------------------------------

(*
   Base module for any PCR.
*)

LOCAL INSTANCE Naturals

VARIABLE map

CONSTANTS InType,       \* Type of PCR input
          CtxIdType,    \* Type of context index
          IndexType,    \* Type of iteration space
          VarPType,     \* Type of producer variable
          VarCType,     \* Type of consumer variable
          VarRType,     \* Type of reducer output         
          NULL          \* Nothing

\* Any PCR can be in exactly one of three states
States == {"OFF","RUN","END"}
         
VarP == [IndexType -> [v : VarPType \union {NULL}, r : Nat]]
VarC == [IndexType -> [v : VarCType \union {NULL}, r : Nat]]                     

\* Any PCR runs in a context. A context is a record with:
CtxType == [in  : InType   ,   \* input
\*            i_p : IndexType,   \* iteration index
            v_p : VarP,        \* producer history
            v_c : VarC,        \* consumer history
            ret : VarRType,    \* reducer result
            ste : States]      \* discrete state     

\* PCR context map. Root context is indexed at <<0>>. 
CtxMap   == [CtxIdType -> CtxType \union {NULL}] 
CtxIndex == {I \in CtxIdType : map[I] # NULL}

\* Convenient names for context elements            
in(I)    == map[I].in
\*i_p(I)   == map[I].i_p
v_p(I)   == map[I].v_p
v_c(I)   == map[I].v_c
Out(I)   == map[I].ret 
State(I) == map[I].ste
In1(I)   == in(I)[1]
In2(I)   == in(I)[2] 
In3(I)   == in(I)[3]
                      
\* Useful predicates on indexes   
WellDef(I)  == map[I] # NULL
Off(I)      == map[I].ste = "OFF"
Running(I)  == map[I].ste = "RUN"
Finished(I) == map[I].ste = "END"
   
\* Useful predicates on vars
Written(var, i) == var[i].v # NULL
Read(var, i)    == var[i].r > 0            
             
\* Auxiliary operators over functions/records
Updf(f, x, v) == [f EXCEPT ![x] = v]
Updr(r, k, v) == [r EXCEPT !.k  = v]   
ExtR(r, s)    == [k \in DOMAIN r |-> IF k \in DOMAIN s THEN s[k] ELSE r[k]]
               
=============================================================================
\* Modification History
\* Last modified Tue Sep 29 14:53:41 UYT 2020 by josedu
\* Last modified Mon Jul 06 15:51:49 UYT 2020 by josed
\* Last modified Tue Jun 09 12:24:42 GMT-03:00 2020 by JosEdu
\* Created Mon Jun 08 22:50:44 GMT-03:00 2020 by JosEdu
