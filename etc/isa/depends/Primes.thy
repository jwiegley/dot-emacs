(*  Title:      HOL/ex/Primes.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The Greatest Common Divisor and Euclid's algorithm

The "simpset" clause in the recdef declaration used to be necessary when the
two lemmas where not part of the default simpset.
*)

Primes = Main +


consts
  is_gcd  :: [nat,nat,nat]=>bool          (*gcd as a relation*)
  gcd     :: "nat*nat=>nat"               (*Euclid's algorithm *)
  coprime :: [nat,nat]=>bool
  prime   :: nat set
  
recdef gcd "measure ((%(m,n).n) ::nat*nat=>nat)"
(*  simpset "simpset() addsimps [mod_less_divisor, zero_less_eq]" *)
    "gcd (m, n) = (if n=0 then m else gcd(n, m mod n))"

defs
  is_gcd_def  "is_gcd p m n == p dvd m  &  p dvd n  &
                               (ALL d. d dvd m & d dvd n --> d dvd p)"

  coprime_def "coprime m n == gcd(m,n) = 1"

  prime_def   "prime == {p. 1<p & (ALL m. m dvd p --> m=1 | m=p)}"

end
