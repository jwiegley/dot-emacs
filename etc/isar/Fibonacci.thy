(* Fibonacci.thy taken from Isabelle distribution
   Gertrud Bauer / Larry Paulson  *)

theory Fibonacci = Primes:

subsection {* Fibonacci numbers *}

consts fib :: "nat => nat"
recdef fib less_than
 "fib 0 = 0"
 "fib (Suc 0) = 1"
 "fib (Suc (Suc x)) = fib x + fib (Suc x)"

lemma [simp]: "0 < fib (Suc n)"
  by (induct n rule: fib.induct) (simp+)


text {* Alternative induction rule. *}

theorem fib_induct:
  "\<lbrakk>P 0; P 1; \<And>n. \<lbrakk>P (n + 1); P n\<rbrakk> \<Longrightarrow> P (n + 2)\<rbrakk> \<Longrightarrow> P (n::nat)"
  by (induct rule: fib.induct, simp+)


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

lemma gcd_fib_Suc_eq_1: "gcd (fib n, fib (n + 1)) = 1" (is "?P n")
proof (induct n rule: fib_induct)
  show "?P 0" by simp
  show "?P 1" by simp
  fix n
  have "fib (n + 2 + 1) = fib (n + 1) + fib (n + 2)"
    by simp
  also have "gcd (fib (n + 2), ...) = gcd (fib (n + 2), fib (n + 1))"
    by (simp only: gcd_add2')
  also have "... = gcd (fib (n + 1), fib (n + 1 + 1))"
    by (simp add: gcd_commute)
  also assume "... = 1"
  finally show "?P (n + 2)" .
qed

lemma gcd_mult_add: "0 < n ==> gcd (n * k + m, n) = gcd (m, n)"
proof -
  assume "0 < n"
  hence "gcd (n * k + m, n) = gcd (n, m mod n)"
    by (simp add: gcd_non_0 add_commute)
  also have "... = gcd (m, n)" by (simp! add: gcd_non_0)
  finally show ?thesis .
qed

lemma gcd_fib_add: "gcd (fib m, fib (n + m)) = gcd (fib m, fib n)"
proof (cases m)
  assume "m = 0"
  thus ?thesis by simp
next
  fix k assume "m = Suc k"
  hence "gcd (fib m, fib (n + m)) = gcd (fib (n + k + 1), fib (k + 1))"
    by (simp add: gcd_commute)
  also have "fib (n + k + 1)
    = fib (k + 1) * fib (n + 1) + fib k * fib n"
    by (rule fib_add)
  also have "gcd (..., fib (k + 1)) = gcd (fib k * fib n, fib (k + 1))"
    by (simp add: gcd_mult_add)
  also have "... = gcd (fib n, fib (k + 1))"
    by (simp only: gcd_fib_Suc_eq_1 gcd_mult_cancel)
  also have "... = gcd (fib m, fib n)"
    by (simp! add: gcd_commute)
  finally show ?thesis .
qed

lemma gcd_fib_diff:
  "m <= n ==> gcd (fib m, fib (n - m)) = gcd (fib m, fib n)"
proof -
  assume "m <= n"
  have "gcd (fib m, fib (n - m)) = gcd (fib m, fib (n - m + m))"
    by (simp add: gcd_fib_add)
  also have "n - m + m = n" by (simp!)
  finally show ?thesis .
qed

lemma gcd_fib_mod:
  "0 < m \<Longrightarrow> gcd (fib m, fib (n mod m)) = gcd (fib m, fib n)"
proof -
  assume m: "0 < m"
  show ?thesis
  proof (induct n rule: nat_less_induct)
    fix n
    assume hyp: "ALL ma. ma < n
      --> gcd (fib m, fib (ma mod m)) = gcd (fib m, fib ma)"
    show "gcd (fib m, fib (n mod m)) = gcd (fib m, fib n)"
    proof -
      have "n mod m = (if n < m then n else (n - m) mod m)"
	by (rule mod_if)
      also have "gcd (fib m, fib ...) = gcd (fib m, fib n)"
      proof cases
	assume "n < m" thus ?thesis by simp
      next
	assume not_lt: "~ n < m" hence le: "m <= n" by simp
	have "n - m < n" by (simp! add: diff_less)
	with hyp have "gcd (fib m, fib ((n - m) mod m))
	  = gcd (fib m, fib (n - m))" by simp
	also from le have "... = gcd (fib m, fib n)"
	  by (rule gcd_fib_diff)
	finally have "gcd (fib m, fib ((n - m) mod m)) =
	  gcd (fib m, fib n)" .
	with not_lt show ?thesis by simp
      qed
      finally show ?thesis .
    qed
  qed
qed


theorem fib_gcd: "fib (gcd (m, n)) = gcd (fib m, fib n)" (is "?P m n")
proof (induct m n rule: gcd_induct)
  fix m show "fib (gcd (m, 0)) = gcd (fib m, fib 0)" by simp
  fix n :: nat assume n: "0 < n"
  hence "gcd (m, n) = gcd (n, m mod n)" by (rule gcd_non_0)
  also assume hyp: "fib ... = gcd (fib n, fib (m mod n))"
  also from n have "... = gcd (fib n, fib m)" by (rule gcd_fib_mod)
  also have "... = gcd (fib m, fib n)" by (rule gcd_commute)
  finally show "fib (gcd (m, n)) = gcd (fib m, fib n)" .
qed

end
