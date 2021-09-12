----------------------------- MODULE ArithUtils -----------------------------

(* 
  Arithmetic utilities.
*)

INSTANCE Integers
INSTANCE Sequences

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

Sqrt(n) == Max({ i \in Nat : i*i <= n })

Divides(n,m) == \E d \in 0..m : m = n * d

Even(n) == Divides(2,n)

Odd(n) == ~ Even(n)

IsPrime(n) == n > 1 /\ ~ \E m \in 2..(n-1) : Divides(m, n)

abs(n) == IF n < 0 THEN -n ELSE n
                      
fibonacci[n \in Nat] == 
  IF n <= 2 
  THEN 1 
  ELSE fibonacci[n-1] + fibonacci[n-2]

seqSum[s \in Seq(Nat)] ==
  IF   s = <<>> 
  THEN 0
  ELSE Head(s) + seqSum[Tail(s)]

Log(x,b) == CHOOSE n \in Nat : TRUE   \* implemented in Java  

vecSum(v1, v2) == [i \in 1..Len(v1) |-> v1[i] + v2[i]] 

=============================================================================
\* Modification History
\* Last modified Mon Jul 05 18:12:01 GMT-03:00 2021 by JosEdu
\* Last modified Wed Feb 24 23:19:55 UYT 2021 by josedu
\* Created Sat Jan 23 00:46:54 UYT 2021 by josedu
