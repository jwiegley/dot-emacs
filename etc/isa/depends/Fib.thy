(*  Title:      ex/Fib
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

The Fibonacci function.  Demonstrates the use of recdef.
*)

Fib = Usedepends + Divides + Primes +

consts fib  :: "nat => nat"
recdef fib "less_than"
  zero    "fib 0 = 0"
  one     "fib 1 = 1"
  Suc_Suc "fib (Suc (Suc x)) = fib x + fib (Suc x)"

end
