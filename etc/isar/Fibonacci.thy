(*  Copied from Isabelle2011-1/src/HOL/Isar_examples/ *)

(*  Title:      HOL/Isar_Examples/Fibonacci.thy
    Author:     Gertrud Bauer
    Copyright   1999 Technische Universitaet Muenchen

The Fibonacci function.  Demonstrates the use of recdef.  Original
tactic script by Lawrence C Paulson.

Fibonacci numbers: proofs of laws taken from

  R. L. Graham, D. E. Knuth, O. Patashnik.
  Concrete Mathematics.
  (Addison-Wesley, 1989)
*)

header {* Fib and Gcd commute *}

theory Fibonacci
imports "~~/src/HOL/Number_Theory/Primes"
begin

text_raw {* \footnote{Isar version by Gertrud Bauer.  Original tactic
  script by Larry Paulson.  A few proofs of laws taken from
  \cite{Concrete-Math}.} *}


declare One_nat_def [simp]


subsection {* Fibonacci numbers *}

fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc x)) = fib x + fib (Suc x)"

lemma [simp]: "fib (Suc n) > 0"
  by (induct n rule: fib.induct) simp_all


text {* Alternative induction rule. *}

theorem fib_induct:
    "P 0 ==> P 1 ==> (!!n. P (n + 1) ==> P n ==> P (n + 2)) ==> P (n::nat)"
  by (induct rule: fib.induct) simp_all


subsection {* Fib and gcd commute *}

text {* A few laws taken from \cite{Concrete-Math}. *}

lemma fib_add:
  "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"
  (is "?P n")
  -- {* see \cite[page 280]{Concrete-Math} *}
proof (induct n rule: fib_induct)
  show "?P 0" by simp
  show "?P 1" by simp
  fix n
  have "fib (n + 2 + k + 1)
    = fib (n + k + 1) + fib (n + 1 + k + 1)" by simp
  also assume "fib (n + k + 1)
    = fib (k + 1) * fib (n + 1) + fib k * fib n"
      (is " _ = ?R1")
  also assume "fib (n + 1 + k + 1)
    = fib (k + 1) * fib (n + 1 + 1) + fib k * fib (n + 1)"
      (is " _ = ?R2")
  also have "?R1 + ?R2
    = fib (k + 1) * fib (n + 2 + 1) + fib k * fib (n + 2)"
    by (simp add: add_mult_distrib2)
  finally show "?P (n + 2)" .
qed

lemma gcd_fib_Suc_eq_1: "gcd (fib n) (fib (n + 1)) = 1" (is "?P n")
proof (induct n rule: fib_induct)
  show "?P 0" by simp
  show "?P 1" by simp
  fix n
  have "fib (n + 2 + 1) = fib (n + 1) + fib (n + 2)"
    by simp
  also have "... = fib (n + 2) + fib (n + 1)" by simp
  also have "gcd (fib (n + 2)) ... = gcd (fib (n + 2)) (fib (n + 1))"
    by (rule gcd_add2_nat)
  also have "... = gcd (fib (n + 1)) (fib (n + 1 + 1))"
    by (simp add: gcd_commute_nat)
  also assume "... = 1"
  finally show "?P (n + 2)" .
qed

lemma gcd_mult_add: "(0::nat) < n ==> gcd (n * k + m) n = gcd m n"
proof -
  assume "0 < n"
  then have "gcd (n * k + m) n = gcd n (m mod n)"
    by (simp add: gcd_non_0_nat add_commute)
  also from `0 < n` have "... = gcd m n" by (simp add: gcd_non_0_nat)
  finally show ?thesis .
qed

lemma gcd_fib_add: "gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)"
proof (cases m)
  case 0
  then show ?thesis by simp
next
  case (Suc k)
  then have "gcd (fib m) (fib (n + m)) = gcd (fib (n + k + 1)) (fib (k + 1))"
    by (simp add: gcd_commute_nat)
  also have "fib (n + k + 1)
      = fib (k + 1) * fib (n + 1) + fib k * fib n"
    by (rule fib_add)
  also have "gcd ... (fib (k + 1)) = gcd (fib k * fib n) (fib (k + 1))"
    by (simp add: gcd_mult_add)
  also have "... = gcd (fib n) (fib (k + 1))"
    by (simp only: gcd_fib_Suc_eq_1 gcd_mult_cancel_nat)
  also have "... = gcd (fib m) (fib n)"
    using Suc by (simp add: gcd_commute_nat)
  finally show ?thesis .
qed

lemma gcd_fib_diff:
  assumes "m <= n"
  shows "gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)"
proof -
  have "gcd (fib m) (fib (n - m)) = gcd (fib m) (fib (n - m + m))"
    by (simp add: gcd_fib_add)
  also from `m <= n` have "n - m + m = n" by simp
  finally show ?thesis .
qed

lemma gcd_fib_mod:
  assumes "0 < m"
  shows "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)"
proof (induct n rule: nat_less_induct)
  case (1 n) note hyp = this
  show ?case
  proof -
    have "n mod m = (if n < m then n else (n - m) mod m)"
      by (rule mod_if)
    also have "gcd (fib m) (fib ...) = gcd (fib m) (fib n)"
    proof (cases "n < m")
      case True then show ?thesis by simp
    next
      case False then have "m <= n" by simp
      from `0 < m` and False have "n - m < n" by simp
      with hyp have "gcd (fib m) (fib ((n - m) mod m))
          = gcd (fib m) (fib (n - m))" by simp
      also have "... = gcd (fib m) (fib n)"
        using `m <= n` by (rule gcd_fib_diff)
      finally have "gcd (fib m) (fib ((n - m) mod m)) =
          gcd (fib m) (fib n)" .
      with False show ?thesis by simp
    qed
    finally show ?thesis .
  qed
qed

theorem fib_gcd: "fib (gcd m n) = gcd (fib m) (fib n)" (is "?P m n")
proof (induct m n rule: gcd_nat_induct)
  fix m show "fib (gcd m 0) = gcd (fib m) (fib 0)" by simp
  fix n :: nat assume n: "0 < n"
  then have "gcd m n = gcd n (m mod n)" by (simp add: gcd_non_0_nat)
  also assume hyp: "fib ... = gcd (fib n) (fib (m mod n))"
  also from n have "... = gcd (fib n) (fib m)" by (rule gcd_fib_mod)
  also have "... = gcd (fib m) (fib n)" by (rule gcd_commute_nat)
  finally show "fib (gcd m n) = gcd (fib m) (fib n)" .
qed

end
