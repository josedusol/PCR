----------------------------- MODULE PCRBase ------------------------------

(*
   Base module for any PCR.
*)

EXTENDS Naturals

VARIABLE map

CONSTANTS InType,       \* Type of PCR input
          LowerBnd(_),
          UpperBnd(_),
          Step(_),
          CtxIdType,
          IndexType,    \* Type of iteration space
          VarPType,     \* Type of producer variable
          VarCType,     \* Type of consumer variable
          VarRType,     \* Type of reducer output         
          NULL          \* What is NULL should be something globally agreed upon,
                        \* so it is defined on Boot module.

OFF == 0
RUN == 1
END == 2
States == {OFF,RUN,END}
         
VarP == [IndexType -> [v : VarPType \union {NULL}, r : Nat]]
VarC == [IndexType -> [v : VarCType \union {NULL}, r : Nat]]                     
VarR == VarRType

\* Any PCR runs in a context. A context is a record with:
CtxType == [in  : InType   ,   \* input
            i_p : IndexType,   \* Iterator index
            v_p : VarP,        \* producer history
            v_c : VarC,        \* consumer history
            ret : VarR,        \* reducer result
            ste : States]      \* status     

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

\* Any PCR have an iteration space: a set of indexes
range(start, end, step(_)) ==
  LET F[i \in IndexType] == 
        IF i <= end
        THEN {i} \union F[step(i)]
        ELSE {}    
  IN  F[start]  
Iterator(i) == range(LowerBnd(in(i)), UpperBnd(in(i)), Step)
Bound(i)    == i_p(i) \in Iterator(i)            
                                    
\* Useful predicates 
Written(var, j) == var[j].v # NULL
Read(var, j)    == var[j].r > 0          
Off(i)          == map[i].ste = OFF
Running(i)      == map[i].ste = RUN
Finished(i)     == map[i].ste = END
State(i)        == map[i].ste
CDone(i, j)     == \A k \in Iterator(i)\{j} : Read(v_c(i), k)                  
Out(i)          == map[i].ret    
        
\* Common actions         
Start(i) == map' = [map EXCEPT ![i].ste = RUN]   
 
Quit(i) == /\ Iterator(i) = {} 
           /\ map' = [map EXCEPT ![i].ste = END]       
             
\* Auxiliary operators over functions/records
Updf(f, x, v) == [f EXCEPT ![x] = v]
Updr(r, k, v) == [r EXCEPT !.k  = v]   
ExtR(r, s)    == [k \in DOMAIN r |-> IF k \in DOMAIN s THEN s[k] ELSE r[k]]
               
=============================================================================
\* Modification History
\* Last modified Sat Sep 12 17:59:42 UYT 2020 by josedu
\* Last modified Mon Jul 06 15:51:49 UYT 2020 by josed
\* Last modified Tue Jun 09 12:24:42 GMT-03:00 2020 by JosEdu
\* Created Mon Jun 08 22:50:44 GMT-03:00 2020 by JosEdu
