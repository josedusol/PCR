------------------------------ MODULE BagUtils ------------------------------

LOCAL INSTANCE Bags

(* The collection of all bags over S *)
BagOf(S) == UNION {[xs -> Nat\{0}] : xs \in SUBSET S}

=============================================================================
\* Modification History
\* Last modified Sun Nov 14 12:55:51 UYT 2021 by josedu
\* Created Sat Jan 23 00:54:12 UYT 2021 by josedu
