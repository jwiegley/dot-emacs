(* Example proof by Larry Paulson; see http://www.cs.kun.nl/~freek/comparison/ 
   Taken from Isabelle2004 distribution. *)


(*  Title:      HOL/Hyperreal/ex/Sqrt_Script.thy
    ID:         Id: Sqrt_Script.thy,v 1.3 2003/12/10 14:59:35 paulson Exp 
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge
*)

header {* Square roots of primes are irrational (script version) *}

theory Sqrt_Script = Primes + Complex_Main:

text {*
  \medskip Contrast this linear Isabelle/Isar script with Markus
  Wenzel's more mathematical version.
*}

subsection {* Preliminaries *}

lemma prime_nonzero:  "p \<in> prime \<Longrightarrow> p \<noteq> 0"
  by (force simp add: prime_def)

lemma prime_dvd_other_side:
    "n * n = p * (k * k) \<Longrightarrow> p \<in> prime \<Longrightarrow> p dvd n"
  apply (subgoal_tac "p dvd n * n", blast dest: prime_dvd_mult)
  apply (rule_tac j = "k * k" in dvd_mult_left, simp)
  done

lemma reduction: "p \<in> prime \<Longrightarrow>
    0 < k \<Longrightarrow> k * k = p * (j * j) \<Longrightarrow> k < p * j \<and> 0 < j"
  apply (rule ccontr)
  apply (simp add: linorder_not_less)
  apply (erule disjE)
   apply (frule mult_le_mono, assumption)
   apply auto
  apply (force simp add: prime_def)
  done

lemma rearrange: "(j::nat) * (p * j) = k * k \<Longrightarrow> k * k = p * (j * j)"
  by (simp add: mult_ac)

lemma prime_not_square:
    "p \<in> prime \<Longrightarrow> (\<And>k. 0 < k \<Longrightarrow> m * m \<noteq> p * (k * k))"
  apply (induct m rule: nat_less_induct)
  apply clarify
  apply (frule prime_dvd_other_side, assumption)
  apply (erule dvdE)
  apply (simp add: nat_mult_eq_cancel_disj prime_nonzero)
  apply (blast dest: rearrange reduction)
  done


subsection {* The set of rational numbers *}

constdefs
  rationals :: "real set"    ("\<rat>")
  "\<rat> \<equiv> {x. \<exists>m n. n \<noteq> 0 \<and> \<bar>x\<bar> = real (m::nat) / real (n::nat)}"


subsection {* Main theorem *}

text {*
  The square root of any prime number (including @{text 2}) is
  irrational.
*}

theorem prime_sqrt_irrational:
    "p \<in> prime \<Longrightarrow> x * x = real p \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<notin> \<rat>"
  apply (simp add: rationals_def real_abs_def)
  apply clarify
  apply (erule_tac P = "real m / real n * ?x = ?y" in rev_mp)
  apply (simp del: real_of_nat_mult
              add: divide_eq_eq prime_not_square real_of_nat_mult [symmetric])
  done

lemmas two_sqrt_irrational =
  prime_sqrt_irrational [OF two_is_prime]

end
