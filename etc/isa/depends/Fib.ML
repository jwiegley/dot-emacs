(*  Title:      HOL/ex/Fib
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1997  University of Cambridge

Fibonacci numbers: proofs of laws taken from

  R. L. Graham, D. E. Knuth, O. Patashnik.
  Concrete Mathematics.
  (Addison-Wesley, 1989)
*)


(** The difficulty in these proofs is to ensure that the induction hypotheses
    are applied before the definition of "fib".  Towards this end, the 
    "fib" equations are not added to the simpset and are applied very 
    selectively at first.
**)

Delsimps fib.Suc_Suc;

val [fib_Suc_Suc] = fib.Suc_Suc;
val fib_Suc3 = read_instantiate [("x", "(Suc ?n)")] fib_Suc_Suc;

(*Concrete Mathematics, page 280*)
Goal "fib (Suc (n + k)) = fib(Suc k) * fib(Suc n) + fib k * fib n";
by (res_inst_tac [("u","n")] fib.induct 1);
(*Simplify the LHS just enough to apply the induction hypotheses*)
by (asm_full_simp_tac
    (simpset() addsimps [inst "x" "Suc(?m+?n)" fib_Suc_Suc]) 3);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps 
		   ([fib_Suc_Suc, add_mult_distrib, add_mult_distrib2]))));
qed "fib_add";


Goal "fib (Suc n) ~= 0";
by (res_inst_tac [("u","n")] fib.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [fib_Suc_Suc])));
qed "fib_Suc_neq_0";

(* Also add  0 < fib (Suc n) *)
Addsimps [fib_Suc_neq_0, [neq0_conv, fib_Suc_neq_0] MRS iffD1];

Goal "0<n ==> 0 < fib n";
by (rtac (not0_implies_Suc RS exE) 1);
by Auto_tac;
qed "fib_gr_0";

(*Concrete Mathematics, page 278: Cassini's identity.
  It is much easier to prove using integers!*)
Goal "int (fib (Suc (Suc n)) * fib n) = \
\     (if n mod 2 = 0 then int (fib(Suc n) * fib(Suc n)) - #1 \
\                     else int (fib(Suc n) * fib(Suc n)) + #1)";
by (res_inst_tac [("u","n")] fib.induct 1);
by (simp_tac (simpset() addsimps [fib_Suc_Suc, mod_Suc]) 2);
by (simp_tac (simpset() addsimps [fib_Suc_Suc]) 1);
by (asm_full_simp_tac
     (simpset() addsimps [fib_Suc_Suc, add_mult_distrib, add_mult_distrib2, 
			  mod_Suc, zmult_int RS sym] @ zmult_ac) 1);
qed "fib_Cassini";



(** Towards Law 6.111 of Concrete Mathematics **)

Goal "gcd(fib n, fib (Suc n)) = 1";
by (res_inst_tac [("u","n")] fib.induct 1);
by (asm_simp_tac (simpset() addsimps [fib_Suc3, gcd_commute, gcd_add2]) 3);
by (ALLGOALS (simp_tac (simpset() addsimps [fib_Suc_Suc])));
qed "gcd_fib_Suc_eq_1"; 

val gcd_fib_commute = 
    read_instantiate_sg (sign_of thy) [("m", "fib m")] gcd_commute;

Goal "gcd(fib m, fib (n+m)) = gcd(fib m, fib n)";
by (simp_tac (simpset() addsimps [gcd_fib_commute]) 1);
by (case_tac "m=0" 1);
by (Asm_simp_tac 1);
by (clarify_tac (claset() addSDs [not0_implies_Suc]) 1);
by (simp_tac (simpset() addsimps [fib_add]) 1);
by (asm_simp_tac (simpset() addsimps [add_commute, gcd_non_0]) 1);
by (asm_simp_tac (simpset() addsimps [gcd_non_0 RS sym]) 1);
by (asm_simp_tac (simpset() addsimps [gcd_fib_Suc_eq_1, gcd_mult_cancel]) 1);
qed "gcd_fib_add";

Goal "m <= n ==> gcd(fib m, fib (n-m)) = gcd(fib m, fib n)";
by (rtac (gcd_fib_add RS sym RS trans) 1);
by (Asm_simp_tac 1);
qed "gcd_fib_diff";

Goal "0<m ==> gcd (fib m, fib (n mod m)) = gcd (fib m, fib n)";
by (res_inst_tac [("n","n")] less_induct 1);
by (stac mod_if 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [gcd_fib_diff, mod_geq, 
				      not_less_iff_le, diff_less]) 1);
qed "gcd_fib_mod";

(*Law 6.111*)
Goal "fib(gcd(m,n)) = gcd(fib m, fib n)";
by (res_inst_tac [("m","m"),("n","n")] gcd_induct 1);
by (Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [gcd_non_0]) 1);
by (asm_full_simp_tac (simpset() addsimps [gcd_commute, gcd_fib_mod]) 1);
qed "fib_gcd";
