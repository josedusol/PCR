------------------------------ MODULE SeqUtils ------------------------------

EXTENDS Functions

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

SeqFoldL(seq, b, op(_,_)) ==
  LET f[s \in Seq(Range(seq))] == 
        IF s = <<>> 
        THEN b 
        ELSE op(f[Tail(s)], Head(s))
  IN  f[seq]
  
SeqFoldR(seq, b, op(_,_)) ==
  LET f[s \in Seq(Range(seq))] == 
        IF s = <<>> 
        THEN b 
        ELSE op(Head(s), f[Tail(s)])
  IN  f[seq]  
  
SeqFlatten(seq) == 
  LET f[s \in Seq(Range(seq))] == 
        IF s = <<>>
        THEN <<>>
        ELSE Head(s) \o f[Tail(s)]    
  IN  f[seq]  
  
x \uplus y ==
  LET F[s1, s2 \in Seq(Range(x) \union Range(y))] ==
        IF s1 = << >> 
        THEN s2 
        ELSE IF s2 = << >> 
             THEN s1 
             ELSE CASE Head(s1) <= Head(s2) -> <<Head(s1)>> \o F[Tail(s1), s2]
                    [] Head(s1) > Head(s2)  -> <<Head(s2)>> \o F[s1, Tail(s2)]
  IN F[x, y]  

IsOrdered(seq) == 
  \/ Len(seq) <= 1
  \/ LET n == 2..Len(seq) IN \A k \in n: seq[k-1] <= seq[k]

Map(f(_), seq) == [i \in DOMAIN seq |-> f(seq[i])]

l ... u == [i \in l..u |-> i]

=============================================================================
\* Modification History
\* Last modified Wed Sep 08 20:12:59 UYT 2021 by josedu
\* Created Sat Jan 23 00:54:12 UYT 2021 by josedu
