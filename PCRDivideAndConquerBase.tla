---------------------- MODULE PCRDivideAndConquerBase ----------------------

(*
   Main module for PCR MergeSort.
*)

EXTENDS Naturals, Sequences

VARIABLES map

CONSTANTS InType,
          CtxIdType,
          IndexType,
          VarPType,
          VarCType,
          VarRType, 
          NULL

CONSTANTS Partition(_)
         
INSTANCE PCRBase WITH 
  LowerBnd  <- LAMBDA x : 1,
  UpperBnd  <- LAMBDA x : Len(Partition(x)),  
  Step      <- LAMBDA x : x+1  
               
           



=============================================================================
\* Modification History
\* Last modified Sat Sep 19 00:37:35 UYT 2020 by josedu
\* Last modified Fri Jul 17 16:24:43 UYT 2020 by josed
\* Created Mon Jul 06 12:54:04 UYT 2020 by josed
