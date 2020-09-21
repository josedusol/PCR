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
            i_p : IndexType,   \* iteration index
            v_p : VarP,        \* producer history
            v_c : VarC,        \* consumer history
            ret : VarRType,    \* reducer result
            ste : States]      \* discrete state     

\* PCR context map. Root context is <<0>>. 
CtxMap   == [CtxIdType -> CtxType \union {NULL}] 
CtxIndex == {i \in CtxIdType : map[i] # NULL}

\* Convenient names for context elements            
in(i)  == map[i].in
i_p(i) == map[i].i_p
v_p(i) == map[i].v_p
v_c(i) == map[i].v_c
In1(i) == in(i)[1]
In2(i) == in(i)[2] 
In3(i) == in(i)[3]
                      
\* Useful predicates 
Written(var, j) == var[j].v # NULL
Read(var, j)    == var[j].r > 0          
Off(i)          == map[i].ste = "OFF"
Running(i)      == map[i].ste = "RUN"
Finished(i)     == map[i].ste = "END"
State(i)        == map[i].ste
Out(i)          == map[i].ret    
   
\* Start action         
Start(i) == map' = [map EXCEPT ![i].ste = "RUN"]      
             
\* Auxiliary operators over functions/records
Updf(f, x, v) == [f EXCEPT ![x] = v]
Updr(r, k, v) == [r EXCEPT !.k  = v]   
ExtR(r, s)    == [k \in DOMAIN r |-> IF k \in DOMAIN s THEN s[k] ELSE r[k]]
               
=============================================================================
\* Modification History
\* Last modified Sun Sep 20 21:11:45 UYT 2020 by josedu
\* Last modified Mon Jul 06 15:51:49 UYT 2020 by josed
\* Last modified Tue Jun 09 12:24:42 GMT-03:00 2020 by JosEdu
\* Created Mon Jun 08 22:50:44 GMT-03:00 2020 by JosEdu
