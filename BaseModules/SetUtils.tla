------------------------------ MODULE SetUtils ------------------------------

EXTENDS Functions

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

(*
   Xn(<<S1,S2,...,Sn>>) = S1 \X S2 \X ... \X Sn
*)
Xn(S) == 
  LET U == UNION Range(S)
      FSeq == [1..Len(S) -> U]
  IN  {s \in FSeq : \A i \in 1..Len(s) : s[i] \in S[i]}  

=============================================================================
\* Modification History
\* Last modified Sat Jan 23 00:56:25 UYT 2021 by josedu
\* Created Sat Jan 23 00:55:49 UYT 2021 by josedu
