(*  Title:      HOL/ex/Primes.ML
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge

The "divides" relation, the greatest common divisor and Euclid's algorithm

See H. Davenport, "The Higher Arithmetic".  6th edition.  (CUP, 1992)
*)

eta_contract:=false;

(************************************************)
(** Greatest Common Divisor                    **)
(************************************************)

(*** Euclid's Algorithm ***)


val [gcd_eq] = gcd.simps;


val prems = goal thy
     "[| !!m. P m 0;     \
\        !!m n. [| 0<n;  P n (m mod n) |] ==> P m n  \
\     |] ==> P (m::nat) (n::nat)";
by (res_inst_tac [("u","m"),("v","n")] gcd.induct 1);
by (case_tac "n=0" 1);
by (asm_simp_tac (simpset() addsimps prems) 1);
by Safe_tac;
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "gcd_induct";


Goal "gcd(m,0) = m";
by (Simp_tac 1);
qed "gcd_0";
Addsimps [gcd_0];

Goal "0<n ==> gcd(m,n) = gcd (n, m mod n)";
by (Asm_simp_tac 1);
qed "gcd_non_0";

Delsimps gcd.simps;

Goal "gcd(m,1) = 1";
by (simp_tac (simpset() addsimps [gcd_non_0]) 1);
qed "gcd_1";
Addsimps [gcd_1];

(*gcd(m,n) divides m and n.  The conjunctions don't seem provable separately*)
Goal "(gcd(m,n) dvd m) & (gcd(m,n) dvd n)";
by (res_inst_tac [("m","m"),("n","n")] gcd_induct 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [gcd_non_0])));
by (blast_tac (claset() addDs [dvd_mod_imp_dvd]) 1);
qed "gcd_dvd_both";

bind_thm ("gcd_dvd1", gcd_dvd_both RS conjunct1);
bind_thm ("gcd_dvd2", gcd_dvd_both RS conjunct2);


(*Maximality: for all m,n,f naturals, 
                if f divides m and f divides n then f divides gcd(m,n)*)
Goal "(f dvd m) --> (f dvd n) --> f dvd gcd(m,n)";
by (res_inst_tac [("m","m"),("n","n")] gcd_induct 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps[gcd_non_0, dvd_mod])));
qed_spec_mp "gcd_greatest";

(*Function gcd yields the Greatest Common Divisor*)
Goalw [is_gcd_def] "is_gcd (gcd(m,n)) m n";
by (asm_simp_tac (simpset() addsimps [gcd_greatest, gcd_dvd_both]) 1);
qed "is_gcd";

(*uniqueness of GCDs*)
Goalw [is_gcd_def] "[| is_gcd m a b; is_gcd n a b |] ==> m=n";
by (blast_tac (claset() addIs [dvd_anti_sym]) 1);
qed "is_gcd_unique";

(*USED??*)
Goalw [is_gcd_def]
    "[| is_gcd m a b; k dvd a; k dvd b |] ==> k dvd m";
by (Blast_tac 1);
qed "is_gcd_dvd";

(** Commutativity **)

Goalw [is_gcd_def] "is_gcd k m n = is_gcd k n m";
by (Blast_tac 1);
qed "is_gcd_commute";

Goal "gcd(m,n) = gcd(n,m)";
by (rtac is_gcd_unique 1);
by (rtac is_gcd 2);
by (asm_simp_tac (simpset() addsimps [is_gcd, is_gcd_commute]) 1);
qed "gcd_commute";

Goal "gcd(gcd(k,m),n) = gcd(k,gcd(m,n))";
by (rtac is_gcd_unique 1);
by (rtac is_gcd 2);
by (rewtac is_gcd_def);
by (blast_tac (claset() addSIs [gcd_dvd1, gcd_dvd2]
   	                addIs  [gcd_greatest, dvd_trans]) 1);
qed "gcd_assoc";

Goal "gcd(0,m) = m";
by (stac gcd_commute 1);
by (rtac gcd_0 1);
qed "gcd_0_left";

Goal "gcd(1,m) = 1";
by (stac gcd_commute 1);
by (rtac gcd_1 1);
qed "gcd_1_left";
Addsimps [gcd_0_left, gcd_1_left];


(** Multiplication laws **)

(*Davenport, page 27*)
Goal "k * gcd(m,n) = gcd(k*m, k*n)";
by (res_inst_tac [("m","m"),("n","n")] gcd_induct 1);
by (Asm_full_simp_tac 1);
by (case_tac "k=0" 1);
 by (Asm_full_simp_tac 1);
by (asm_full_simp_tac
    (simpset() addsimps [mod_geq, gcd_non_0, mod_mult_distrib2]) 1);
qed "gcd_mult_distrib2";

Goal "gcd(m,m) = m";
by (cut_inst_tac [("k","m"),("m","1"),("n","1")] gcd_mult_distrib2 1);
by (Asm_full_simp_tac 1);
qed "gcd_self";
Addsimps [gcd_self];

Goal "gcd(k, k*n) = k";
by (cut_inst_tac [("k","k"),("m","1"),("n","n")] gcd_mult_distrib2 1);
by (Asm_full_simp_tac 1);
qed "gcd_mult";
Addsimps [gcd_mult];

Goal "[| gcd(k,n)=1; k dvd (m*n) |] ==> k dvd m";
by (subgoal_tac "m = gcd(m*k, m*n)" 1);
by (etac ssubst 1 THEN rtac gcd_greatest 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [gcd_mult_distrib2 RS sym])));
qed "relprime_dvd_mult";

Goalw [prime_def] "[| p: prime;  ~ p dvd n |] ==> gcd (p, n) = 1";
by (cut_inst_tac [("m","p"),("n","n")] gcd_dvd_both 1);
by Auto_tac;
qed "prime_imp_relprime";

(*This theorem leads immediately to a proof of the uniqueness of factorization.
  If p divides a product of primes then it is one of those primes.*)
Goal "[| p: prime; p dvd (m*n) |] ==> p dvd m | p dvd n";
by (blast_tac (claset() addIs [relprime_dvd_mult, prime_imp_relprime]) 1);
qed "prime_dvd_mult";


(** Addition laws **)

Goal "gcd(m, m+n) = gcd(m,n)";
by (res_inst_tac [("n1", "m+n")] (gcd_commute RS ssubst) 1);
by (rtac (gcd_eq RS trans) 1);
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [mod_add_self1]) 1);
by (stac gcd_commute 1);
by (stac gcd_non_0 1);
by Safe_tac;
qed "gcd_add";

Goal "gcd(m, n+m) = gcd(m,n)";
by (asm_simp_tac (simpset() addsimps [add_commute, gcd_add]) 1);
qed "gcd_add2";

Goal "gcd(m, k*m+n) = gcd(m,n)";
by (induct_tac "k" 1);
by (asm_simp_tac (simpset() addsimps [gcd_add, add_assoc]) 2); 
by (Simp_tac 1);
qed "gcd_add_mult";


(** More multiplication laws **)

Goal "gcd(m,n) dvd gcd(k*m, n)";
by (blast_tac (claset() addIs [gcd_greatest, dvd_trans, 
                               gcd_dvd1, gcd_dvd2]) 1);
qed "gcd_dvd_gcd_mult";

Goal "gcd(k,n) = 1 ==> gcd(k*m, n) = gcd(m,n)";
by (rtac dvd_anti_sym 1);
by (rtac gcd_dvd_gcd_mult 2);
by (rtac ([relprime_dvd_mult, gcd_dvd2] MRS gcd_greatest) 1);
by (stac mult_commute 2);
by (rtac gcd_dvd1 2);
by (stac gcd_commute 1);
by (asm_simp_tac (simpset() addsimps [gcd_assoc RS sym]) 1);
qed "gcd_mult_cancel";
