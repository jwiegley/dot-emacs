(********** This file is from the Isabelle distribution **********)

(*  Title:      HOL/ex/Tarski.thy
    ID:         Id: Tarski.thy,v 1.10 2002/09/26 08:51:32 paulson Exp 
    Author:     Florian Kammüller, Cambridge University Computer Laboratory
*)

header {* The Full Theorem of Tarski *}

theory Tarski = Main + FuncSet:

text {*
  Minimal version of lattice theory plus the full theorem of Tarski:
  The fixedpoints of a complete lattice themselves form a complete
  lattice.

  Illustrates first-class theories, using the Sigma representation of
  structures.  Tidied and converted to Isar by lcp.
*}

record 'a potype =
  pset  :: "'a set"
  order :: "('a * 'a) set"

constdefs
  monotone :: "['a => 'a, 'a set, ('a *'a)set] => bool"
  "monotone f A r == \<forall>x\<in>A. \<forall>y\<in>A. (x, y): r --> ((f x), (f y)) : r"

  least :: "['a => bool, 'a potype] => 'a"
  "least P po == @ x. x: pset po & P x &
                       (\<forall>y \<in> pset po. P y --> (x,y): order po)"

  greatest :: "['a => bool, 'a potype] => 'a"
  "greatest P po == @ x. x: pset po & P x &
                          (\<forall>y \<in> pset po. P y --> (y,x): order po)"

  lub  :: "['a set, 'a potype] => 'a"
  "lub S po == least (%x. \<forall>y\<in>S. (y,x): order po) po"

  glb  :: "['a set, 'a potype] => 'a"
  "glb S po == greatest (%x. \<forall>y\<in>S. (x,y): order po) po"

  isLub :: "['a set, 'a potype, 'a] => bool"
  "isLub S po == %L. (L: pset po & (\<forall>y\<in>S. (y,L): order po) &
                   (\<forall>z\<in>pset po. (\<forall>y\<in>S. (y,z): order po) --> (L,z): order po))"

  isGlb :: "['a set, 'a potype, 'a] => bool"
  "isGlb S po == %G. (G: pset po & (\<forall>y\<in>S. (G,y): order po) &
                 (\<forall>z \<in> pset po. (\<forall>y\<in>S. (z,y): order po) --> (z,G): order po))"

  "fix"    :: "[('a => 'a), 'a set] => 'a set"
  "fix f A  == {x. x: A & f x = x}"

  interval :: "[('a*'a) set,'a, 'a ] => 'a set"
  "interval r a b == {x. (a,x): r & (x,b): r}"


constdefs
  Bot :: "'a potype => 'a"
  "Bot po == least (%x. True) po"

  Top :: "'a potype => 'a"
  "Top po == greatest (%x. True) po"

  PartialOrder :: "('a potype) set"
  "PartialOrder == {P. refl (pset P) (order P) & antisym (order P) &
                       trans (order P)}"

  CompleteLattice :: "('a potype) set"
  "CompleteLattice == {cl. cl: PartialOrder &
                        (\<forall>S. S <= pset cl --> (\<exists>L. isLub S cl L)) &
                        (\<forall>S. S <= pset cl --> (\<exists>G. isGlb S cl G))}"

  CLF :: "('a potype * ('a => 'a)) set"
  "CLF == SIGMA cl: CompleteLattice.
            {f. f: pset cl -> pset cl & monotone f (pset cl) (order cl)}"

  induced :: "['a set, ('a * 'a) set] => ('a *'a)set"
  "induced A r == {(a,b). a : A & b: A & (a,b): r}"


constdefs
  sublattice :: "('a potype * 'a set)set"
  "sublattice ==
      SIGMA cl: CompleteLattice.
          {S. S <= pset cl &
           (| pset = S, order = induced S (order cl) |): CompleteLattice }"

syntax
  "@SL"  :: "['a set, 'a potype] => bool" ("_ <<= _" [51,50]50)

translations
  "S <<= cl" == "S : sublattice `` {cl}"

constdefs
  dual :: "'a potype => 'a potype"
  "dual po == (| pset = pset po, order = converse (order po) |)"

locale (open) PO =
  fixes cl :: "'a potype"
    and A  :: "'a set"
    and r  :: "('a * 'a) set"
  assumes cl_po:  "cl : PartialOrder"
  defines A_def: "A == pset cl"
     and  r_def: "r == order cl"

locale (open) CL = PO +
  assumes cl_co:  "cl : CompleteLattice"

locale (open) CLF = CL +
  fixes f :: "'a => 'a"
    and P :: "'a set"
  assumes f_cl:  "(cl,f) : CLF" (*was the equivalent "f : CLF``{cl}"*)
  defines P_def: "P == fix f A"


locale (open) Tarski = CLF +
  fixes Y     :: "'a set"
    and intY1 :: "'a set"
    and v     :: "'a"
  assumes
    Y_ss: "Y <= P"
  defines
    intY1_def: "intY1 == interval r (lub Y cl) (Top cl)"
    and v_def: "v == glb {x. ((%x: intY1. f x) x, x): induced intY1 r &
                             x: intY1}
                      (| pset=intY1, order=induced intY1 r|)"


subsubsection {* Partial Order *}

lemma (in PO) PO_imp_refl: "refl A r"
apply (insert cl_po)
apply (simp add: PartialOrder_def A_def r_def)
done

lemma (in PO) PO_imp_sym: "antisym r"
apply (insert cl_po)
apply (simp add: PartialOrder_def A_def r_def)
done

lemma (in PO) PO_imp_trans: "trans r"
apply (insert cl_po)
apply (simp add: PartialOrder_def A_def r_def)
done

lemma (in PO) reflE: "[| refl A r; x \<in> A|] ==> (x, x) \<in> r"
apply (insert cl_po)
apply (simp add: PartialOrder_def refl_def)
done

lemma (in PO) antisymE: "[| antisym r; (a, b) \<in> r; (b, a) \<in> r |] ==> a = b"
apply (insert cl_po)
apply (simp add: PartialOrder_def antisym_def)
done

lemma (in PO) transE: "[| trans r; (a, b) \<in> r; (b, c) \<in> r|] ==> (a,c) \<in> r"
apply (insert cl_po)
apply (simp add: PartialOrder_def)
apply (unfold trans_def, fast)
done

lemma (in PO) monotoneE:
     "[| monotone f A r;  x \<in> A; y \<in> A; (x, y) \<in> r |] ==> (f x, f y) \<in> r"
by (simp add: monotone_def)

lemma (in PO) po_subset_po:
     "S <= A ==> (| pset = S, order = induced S r |) \<in> PartialOrder"
apply (simp (no_asm) add: PartialOrder_def)
apply auto
-- {* refl *}
apply (simp add: refl_def induced_def)
apply (blast intro: PO_imp_refl [THEN reflE])
-- {* antisym *}
apply (simp add: antisym_def induced_def)
apply (blast intro: PO_imp_sym [THEN antisymE])
-- {* trans *}
apply (simp add: trans_def induced_def)
apply (blast intro: PO_imp_trans [THEN transE])
done

lemma (in PO) indE: "[| (x, y) \<in> induced S r; S <= A |] ==> (x, y) \<in> r"
by (simp add: add: induced_def)

lemma (in PO) indI: "[| (x, y) \<in> r; x \<in> S; y \<in> S |] ==> (x, y) \<in> induced S r"
by (simp add: add: induced_def)

lemma (in CL) CL_imp_ex_isLub: "S <= A ==> \<exists>L. isLub S cl L"
apply (insert cl_co)
apply (simp add: CompleteLattice_def A_def)
done

declare (in CL) cl_co [simp]

lemma isLub_lub: "(\<exists>L. isLub S cl L) = isLub S cl (lub S cl)"
by (simp add: lub_def least_def isLub_def some_eq_ex [symmetric])

lemma isGlb_glb: "(\<exists>G. isGlb S cl G) = isGlb S cl (glb S cl)"
by (simp add: glb_def greatest_def isGlb_def some_eq_ex [symmetric])

lemma isGlb_dual_isLub: "isGlb S cl = isLub S (dual cl)"
by (simp add: isLub_def isGlb_def dual_def converse_def)

lemma isLub_dual_isGlb: "isLub S cl = isGlb S (dual cl)"
by (simp add: isLub_def isGlb_def dual_def converse_def)

lemma (in PO) dualPO: "dual cl \<in> PartialOrder"
apply (insert cl_po)
apply (simp add: PartialOrder_def dual_def refl_converse
                 trans_converse antisym_converse)
done

lemma Rdual:
     "\<forall>S. (S <= A -->( \<exists>L. isLub S (| pset = A, order = r|) L))
      ==> \<forall>S. (S <= A --> (\<exists>G. isGlb S (| pset = A, order = r|) G))"
apply safe
apply (rule_tac x = "lub {y. y \<in> A & (\<forall>k \<in> S. (y, k) \<in> r)}
                      (|pset = A, order = r|) " in exI)
apply (drule_tac x = "{y. y \<in> A & (\<forall>k \<in> S. (y,k) \<in> r) }" in spec)
apply (drule mp, fast)
apply (simp add: isLub_lub isGlb_def)
apply (simp add: isLub_def, blast)
done

lemma lub_dual_glb: "lub S cl = glb S (dual cl)"
by (simp add: lub_def glb_def least_def greatest_def dual_def converse_def)

lemma glb_dual_lub: "glb S cl = lub S (dual cl)"
by (simp add: lub_def glb_def least_def greatest_def dual_def converse_def)

lemma CL_subset_PO: "CompleteLattice <= PartialOrder"
by (simp add: PartialOrder_def CompleteLattice_def, fast)

lemmas CL_imp_PO = CL_subset_PO [THEN subsetD]

declare CL_imp_PO [THEN Tarski.PO_imp_refl, simp]
declare CL_imp_PO [THEN Tarski.PO_imp_sym, simp]
declare CL_imp_PO [THEN Tarski.PO_imp_trans, simp]

lemma (in CL) CO_refl: "refl A r"
by (rule PO_imp_refl)

lemma (in CL) CO_antisym: "antisym r"
by (rule PO_imp_sym)

lemma (in CL) CO_trans: "trans r"
by (rule PO_imp_trans)

lemma CompleteLatticeI:
     "[| po \<in> PartialOrder; (\<forall>S. S <= pset po --> (\<exists>L. isLub S po L));
         (\<forall>S. S <= pset po --> (\<exists>G. isGlb S po G))|]
      ==> po \<in> CompleteLattice"
apply (unfold CompleteLattice_def, blast)
done

lemma (in CL) CL_dualCL: "dual cl \<in> CompleteLattice"
apply (insert cl_co)
apply (simp add: CompleteLattice_def dual_def)
apply (fold dual_def)
apply (simp add: isLub_dual_isGlb [symmetric] isGlb_dual_isLub [symmetric]
                 dualPO)
done

lemma (in PO) dualA_iff: "pset (dual cl) = pset cl"
by (simp add: dual_def)

lemma (in PO) dualr_iff: "((x, y) \<in> (order(dual cl))) = ((y, x) \<in> order cl)"
by (simp add: dual_def)

lemma (in PO) monotone_dual:
     "monotone f (pset cl) (order cl) 
     ==> monotone f (pset (dual cl)) (order(dual cl))"
by (simp add: monotone_def dualA_iff dualr_iff)

lemma (in PO) interval_dual:
     "[| x \<in> A; y \<in> A|] ==> interval r x y = interval (order(dual cl)) y x"
apply (simp add: interval_def dualr_iff)
apply (fold r_def, fast)
done

lemma (in PO) interval_not_empty:
     "[| trans r; interval r a b \<noteq> {} |] ==> (a, b) \<in> r"
apply (simp add: interval_def)
apply (unfold trans_def, blast)
done

lemma (in PO) interval_imp_mem: "x \<in> interval r a b ==> (a, x) \<in> r"
by (simp add: interval_def)

lemma (in PO) left_in_interval:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |] ==> a \<in> interval r a b"
apply (simp (no_asm_simp) add: interval_def)
apply (simp add: PO_imp_trans interval_not_empty)
apply (simp add: PO_imp_refl [THEN reflE])
done

lemma (in PO) right_in_interval:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |] ==> b \<in> interval r a b"
apply (simp (no_asm_simp) add: interval_def)
apply (simp add: PO_imp_trans interval_not_empty)
apply (simp add: PO_imp_refl [THEN reflE])
done


subsubsection {* sublattice *}

lemma (in PO) sublattice_imp_CL:
     "S <<= cl  ==> (| pset = S, order = induced S r |) \<in> CompleteLattice"
by (simp add: sublattice_def CompleteLattice_def A_def r_def)

lemma (in CL) sublatticeI:
     "[| S <= A; (| pset = S, order = induced S r |) \<in> CompleteLattice |]
      ==> S <<= cl"
by (simp add: sublattice_def A_def r_def)


subsubsection {* lub *}

lemma (in CL) lub_unique: "[| S <= A; isLub S cl x; isLub S cl L|] ==> x = L"
apply (rule antisymE)
apply (rule CO_antisym)
apply (auto simp add: isLub_def r_def)
done

lemma (in CL) lub_upper: "[|S <= A; x \<in> S|] ==> (x, lub S cl) \<in> r"
apply (rule CL_imp_ex_isLub [THEN exE], assumption)
apply (unfold lub_def least_def)
apply (rule some_equality [THEN ssubst])
  apply (simp add: isLub_def)
 apply (simp add: lub_unique A_def isLub_def)
apply (simp add: isLub_def r_def)
done

lemma (in CL) lub_least:
     "[| S <= A; L \<in> A; \<forall>x \<in> S. (x,L) \<in> r |] ==> (lub S cl, L) \<in> r"
apply (rule CL_imp_ex_isLub [THEN exE], assumption)
apply (unfold lub_def least_def)
apply (rule_tac s=x in some_equality [THEN ssubst])
  apply (simp add: isLub_def)
 apply (simp add: lub_unique A_def isLub_def)
apply (simp add: isLub_def r_def A_def)
done

lemma (in CL) lub_in_lattice: "S <= A ==> lub S cl \<in> A"
apply (rule CL_imp_ex_isLub [THEN exE], assumption)
apply (unfold lub_def least_def)
apply (subst some_equality)
apply (simp add: isLub_def)
prefer 2 apply (simp add: isLub_def A_def)
apply (simp add: lub_unique A_def isLub_def)
done

lemma (in CL) lubI:
     "[| S <= A; L \<in> A; \<forall>x \<in> S. (x,L) \<in> r;
         \<forall>z \<in> A. (\<forall>y \<in> S. (y,z) \<in> r) --> (L,z) \<in> r |] ==> L = lub S cl"
apply (rule lub_unique, assumption)
apply (simp add: isLub_def A_def r_def)
apply (unfold isLub_def)
apply (rule conjI)
apply (fold A_def r_def)
apply (rule lub_in_lattice, assumption)
apply (simp add: lub_upper lub_least)
done

lemma (in CL) lubIa: "[| S <= A; isLub S cl L |] ==> L = lub S cl"
by (simp add: lubI isLub_def A_def r_def)

lemma (in CL) isLub_in_lattice: "isLub S cl L ==> L \<in> A"
by (simp add: isLub_def  A_def)

lemma (in CL) isLub_upper: "[|isLub S cl L; y \<in> S|] ==> (y, L) \<in> r"
by (simp add: isLub_def r_def)

lemma (in CL) isLub_least:
     "[| isLub S cl L; z \<in> A; \<forall>y \<in> S. (y, z) \<in> r|] ==> (L, z) \<in> r"
by (simp add: isLub_def A_def r_def)

lemma (in CL) isLubI:
     "[| L \<in> A; \<forall>y \<in> S. (y, L) \<in> r;
         (\<forall>z \<in> A. (\<forall>y \<in> S. (y, z):r) --> (L, z) \<in> r)|] ==> isLub S cl L"
by (simp add: isLub_def A_def r_def)


subsubsection {* glb *}

lemma (in CL) glb_in_lattice: "S <= A ==> glb S cl \<in> A"
apply (subst glb_dual_lub)
apply (simp add: A_def)
apply (rule dualA_iff [THEN subst])
apply (rule Tarski.lub_in_lattice)
apply (rule dualPO)
apply (rule CL_dualCL)
apply (simp add: dualA_iff)
done

lemma (in CL) glb_lower: "[|S <= A; x \<in> S|] ==> (glb S cl, x) \<in> r"
apply (subst glb_dual_lub)
apply (simp add: r_def)
apply (rule dualr_iff [THEN subst])
apply (rule Tarski.lub_upper [rule_format])
apply (rule dualPO)
apply (rule CL_dualCL)
apply (simp add: dualA_iff A_def, assumption)
done

text {*
  Reduce the sublattice property by using substructural properties;
  abandoned see @{text "Tarski_4.ML"}.
*}

lemma (in CLF) [simp]:
    "f: pset cl -> pset cl & monotone f (pset cl) (order cl)"
apply (insert f_cl)
apply (simp add: CLF_def)
done

declare (in CLF) f_cl [simp]


lemma (in CLF) f_in_funcset: "f \<in> A -> A"
by (simp add: A_def)

lemma (in CLF) monotone_f: "monotone f A r"
by (simp add: A_def r_def)

lemma (in CLF) CLF_dual: "(cl,f) \<in> CLF ==> (dual cl, f) \<in> CLF"
apply (simp add: CLF_def  CL_dualCL monotone_dual)
apply (simp add: dualA_iff)
done


subsubsection {* fixed points *}

lemma fix_subset: "fix f A <= A"
by (simp add: fix_def, fast)

lemma fix_imp_eq: "x \<in> fix f A ==> f x = x"
by (simp add: fix_def)

lemma fixf_subset:
     "[| A <= B; x \<in> fix (%y: A. f y) A |] ==> x \<in> fix f B"
apply (simp add: fix_def, auto)
done


subsubsection {* lemmas for Tarski, lub *}
lemma (in CLF) lubH_le_flubH:
     "H = {x. (x, f x) \<in> r & x \<in> A} ==> (lub H cl, f (lub H cl)) \<in> r"
apply (rule lub_least, fast)
apply (rule f_in_funcset [THEN funcset_mem])
apply (rule lub_in_lattice, fast)
-- {* @{text "\<forall>x:H. (x, f (lub H r)) \<in> r"} *}
apply (rule ballI)
apply (rule transE)
apply (rule CO_trans)
-- {* instantiates @{text "(x, ???z) \<in> order cl to (x, f x)"}, *}
-- {* because of the def of @{text H} *}
apply fast
-- {* so it remains to show @{text "(f x, f (lub H cl)) \<in> r"} *}
apply (rule_tac f = "f" in monotoneE)
apply (rule monotone_f, fast)
apply (rule lub_in_lattice, fast)
apply (rule lub_upper, fast)
apply assumption
done

lemma (in CLF) flubH_le_lubH:
     "[|  H = {x. (x, f x) \<in> r & x \<in> A} |] ==> (f (lub H cl), lub H cl) \<in> r"
apply (rule lub_upper, fast)
apply (rule_tac t = "H" in ssubst, assumption)
apply (rule CollectI)
apply (rule conjI)
apply (rule_tac [2] f_in_funcset [THEN funcset_mem])
apply (rule_tac [2] lub_in_lattice)
prefer 2 apply fast
apply (rule_tac f = "f" in monotoneE)
apply (rule monotone_f)
  apply (blast intro: lub_in_lattice)
 apply (blast intro: lub_in_lattice f_in_funcset [THEN funcset_mem])
apply (simp add: lubH_le_flubH)
done

lemma (in CLF) lubH_is_fixp:
     "H = {x. (x, f x) \<in> r & x \<in> A} ==> lub H cl \<in> fix f A"
apply (simp add: fix_def)
apply (rule conjI)
apply (rule lub_in_lattice, fast)
apply (rule antisymE)
apply (rule CO_antisym)
apply (simp add: flubH_le_lubH)
apply (simp add: lubH_le_flubH)
done

lemma (in CLF) fix_in_H:
     "[| H = {x. (x, f x) \<in> r & x \<in> A};  x \<in> P |] ==> x \<in> H"
by (simp add: P_def fix_imp_eq [of _ f A] reflE CO_refl
                    fix_subset [of f A, THEN subsetD])

lemma (in CLF) fixf_le_lubH:
     "H = {x. (x, f x) \<in> r & x \<in> A} ==> \<forall>x \<in> fix f A. (x, lub H cl) \<in> r"
apply (rule ballI)
apply (rule lub_upper, fast)
apply (rule fix_in_H)
apply (simp_all add: P_def)
done

lemma (in CLF) lubH_least_fixf:
     "H = {x. (x, f x) \<in> r & x \<in> A}
      ==> \<forall>L. (\<forall>y \<in> fix f A. (y,L) \<in> r) --> (lub H cl, L) \<in> r"
apply (rule allI)
apply (rule impI)
apply (erule bspec)
apply (rule lubH_is_fixp, assumption)
done

subsubsection {* Tarski fixpoint theorem 1, first part *}
lemma (in CLF) T_thm_1_lub: "lub P cl = lub {x. (x, f x) \<in> r & x \<in> A} cl"
apply (rule sym)
apply (simp add: P_def)
apply (rule lubI)
apply (rule fix_subset)
apply (rule lub_in_lattice, fast)
apply (simp add: fixf_le_lubH)
apply (simp add: lubH_least_fixf)
done

lemma (in CLF) glbH_is_fixp: "H = {x. (f x, x) \<in> r & x \<in> A} ==> glb H cl \<in> P"
  -- {* Tarski for glb *}
apply (simp add: glb_dual_lub P_def A_def r_def)
apply (rule dualA_iff [THEN subst])
apply (rule Tarski.lubH_is_fixp)
apply (rule dualPO)
apply (rule CL_dualCL)
apply (rule f_cl [THEN CLF_dual])
apply (simp add: dualr_iff dualA_iff)
done

lemma (in CLF) T_thm_1_glb: "glb P cl = glb {x. (f x, x) \<in> r & x \<in> A} cl"
apply (simp add: glb_dual_lub P_def A_def r_def)
apply (rule dualA_iff [THEN subst])
apply (simp add: Tarski.T_thm_1_lub [of _ f, OF dualPO CL_dualCL]
                 dualPO CL_dualCL CLF_dual dualr_iff)
done

subsubsection {* interval *}

lemma (in CLF) rel_imp_elem: "(x, y) \<in> r ==> x \<in> A"
apply (insert CO_refl)
apply (simp add: refl_def, blast)
done

lemma (in CLF) interval_subset: "[| a \<in> A; b \<in> A |] ==> interval r a b <= A"
apply (simp add: interval_def)
apply (blast intro: rel_imp_elem)
done

lemma (in CLF) intervalI:
     "[| (a, x) \<in> r; (x, b) \<in> r |] ==> x \<in> interval r a b"
apply (simp add: interval_def)
done

lemma (in CLF) interval_lemma1:
     "[| S <= interval r a b; x \<in> S |] ==> (a, x) \<in> r"
apply (unfold interval_def, fast)
done

lemma (in CLF) interval_lemma2:
     "[| S <= interval r a b; x \<in> S |] ==> (x, b) \<in> r"
apply (unfold interval_def, fast)
done

lemma (in CLF) a_less_lub:
     "[| S <= A; S \<noteq> {};
         \<forall>x \<in> S. (a,x) \<in> r; \<forall>y \<in> S. (y, L) \<in> r |] ==> (a,L) \<in> r"
by (blast intro: transE PO_imp_trans)

lemma (in CLF) glb_less_b:
     "[| S <= A; S \<noteq> {};
         \<forall>x \<in> S. (x,b) \<in> r; \<forall>y \<in> S. (G, y) \<in> r |] ==> (G,b) \<in> r"
by (blast intro: transE PO_imp_trans)

lemma (in CLF) S_intv_cl:
     "[| a \<in> A; b \<in> A; S <= interval r a b |]==> S <= A"
by (simp add: subset_trans [OF _ interval_subset])

lemma (in CLF) L_in_interval:
     "[| a \<in> A; b \<in> A; S <= interval r a b;
         S \<noteq> {}; isLub S cl L; interval r a b \<noteq> {} |] ==> L \<in> interval r a b"
apply (rule intervalI)
apply (rule a_less_lub)
prefer 2 apply assumption
apply (simp add: S_intv_cl)
apply (rule ballI)
apply (simp add: interval_lemma1)
apply (simp add: isLub_upper)
-- {* @{text "(L, b) \<in> r"} *}
apply (simp add: isLub_least interval_lemma2)
done

lemma (in CLF) G_in_interval:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {}; S <= interval r a b; isGlb S cl G;
         S \<noteq> {} |] ==> G \<in> interval r a b"
apply (simp add: interval_dual)
apply (simp add: Tarski.L_in_interval [of _ f]
                 dualA_iff A_def dualPO CL_dualCL CLF_dual isGlb_dual_isLub)
done

lemma (in CLF) intervalPO:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |]
      ==> (| pset = interval r a b, order = induced (interval r a b) r |)
          \<in> PartialOrder"
apply (rule po_subset_po)
apply (simp add: interval_subset)
done

lemma (in CLF) intv_CL_lub:
 "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |]
  ==> \<forall>S. S <= interval r a b -->
          (\<exists>L. isLub S (| pset = interval r a b,
                          order = induced (interval r a b) r |)  L)"
apply (intro strip)
apply (frule S_intv_cl [THEN CL_imp_ex_isLub])
prefer 2 apply assumption
apply assumption
apply (erule exE)
-- {* define the lub for the interval as *}
apply (rule_tac x = "if S = {} then a else L" in exI)
apply (simp (no_asm_simp) add: isLub_def split del: split_if)
apply (intro impI conjI)
-- {* @{text "(if S = {} then a else L) \<in> interval r a b"} *}
apply (simp add: CL_imp_PO L_in_interval)
apply (simp add: left_in_interval)
-- {* lub prop 1 *}
apply (case_tac "S = {}")
-- {* @{text "S = {}, y \<in> S = False => everything"} *}
apply fast
-- {* @{text "S \<noteq> {}"} *}
apply simp
-- {* @{text "\<forall>y:S. (y, L) \<in> induced (interval r a b) r"} *}
apply (rule ballI)
apply (simp add: induced_def  L_in_interval)
apply (rule conjI)
apply (rule subsetD)
apply (simp add: S_intv_cl, assumption)
apply (simp add: isLub_upper)
-- {* @{text "\<forall>z:interval r a b. (\<forall>y:S. (y, z) \<in> induced (interval r a b) r \<longrightarrow> (if S = {} then a else L, z) \<in> induced (interval r a b) r"} *}
apply (rule ballI)
apply (rule impI)
apply (case_tac "S = {}")
-- {* @{text "S = {}"} *}
apply simp
apply (simp add: induced_def  interval_def)
apply (rule conjI)
apply (rule reflE)
apply (rule CO_refl, assumption)
apply (rule interval_not_empty)
apply (rule CO_trans)
apply (simp add: interval_def)
-- {* @{text "S \<noteq> {}"} *}
apply simp
apply (simp add: induced_def  L_in_interval)
apply (rule isLub_least, assumption)
apply (rule subsetD)
prefer 2 apply assumption
apply (simp add: S_intv_cl, fast)
done

lemmas (in CLF) intv_CL_glb = intv_CL_lub [THEN Rdual]

lemma (in CLF) interval_is_sublattice:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |]
        ==> interval r a b <<= cl"
apply (rule sublatticeI)
apply (simp add: interval_subset)
apply (rule CompleteLatticeI)
apply (simp add: intervalPO)
 apply (simp add: intv_CL_lub)
apply (simp add: intv_CL_glb)
done

lemmas (in CLF) interv_is_compl_latt =
    interval_is_sublattice [THEN sublattice_imp_CL]


subsubsection {* Top and Bottom *}
lemma (in CLF) Top_dual_Bot: "Top cl = Bot (dual cl)"
by (simp add: Top_def Bot_def least_def greatest_def dualA_iff dualr_iff)

lemma (in CLF) Bot_dual_Top: "Bot cl = Top (dual cl)"
by (simp add: Top_def Bot_def least_def greatest_def dualA_iff dualr_iff)

lemma (in CLF) Bot_in_lattice: "Bot cl \<in> A"
apply (simp add: Bot_def least_def)
apply (rule someI2)
apply (fold A_def)
apply (erule_tac [2] conjunct1)
apply (rule conjI)
apply (rule glb_in_lattice)
apply (rule subset_refl)
apply (fold r_def)
apply (simp add: glb_lower)
done

lemma (in CLF) Top_in_lattice: "Top cl \<in> A"
apply (simp add: Top_dual_Bot A_def)
apply (rule dualA_iff [THEN subst])
apply (blast intro!: Tarski.Bot_in_lattice dualPO CL_dualCL CLF_dual f_cl)
done

lemma (in CLF) Top_prop: "x \<in> A ==> (x, Top cl) \<in> r"
apply (simp add: Top_def greatest_def)
apply (rule someI2)
apply (fold r_def  A_def)
prefer 2 apply fast
apply (intro conjI ballI)
apply (rule_tac [2] lub_upper)
apply (auto simp add: lub_in_lattice)
done

lemma (in CLF) Bot_prop: "x \<in> A ==> (Bot cl, x) \<in> r"
apply (simp add: Bot_dual_Top r_def)
apply (rule dualr_iff [THEN subst])
apply (simp add: Tarski.Top_prop [of _ f]
                 dualA_iff A_def dualPO CL_dualCL CLF_dual)
done

lemma (in CLF) Top_intv_not_empty: "x \<in> A  ==> interval r x (Top cl) \<noteq> {}"
apply (rule notI)
apply (drule_tac a = "Top cl" in equals0D)
apply (simp add: interval_def)
apply (simp add: refl_def Top_in_lattice Top_prop)
done

lemma (in CLF) Bot_intv_not_empty: "x \<in> A ==> interval r (Bot cl) x \<noteq> {}"
apply (simp add: Bot_dual_Top)
apply (subst interval_dual)
prefer 2 apply assumption
apply (simp add: A_def)
apply (rule dualA_iff [THEN subst])
apply (blast intro!: Tarski.Top_in_lattice
                 f_cl dualPO CL_dualCL CLF_dual)
apply (simp add: Tarski.Top_intv_not_empty [of _ f]
                 dualA_iff A_def dualPO CL_dualCL CLF_dual)
done

subsubsection {* fixed points form a partial order *}

lemma (in CLF) fixf_po: "(| pset = P, order = induced P r|) \<in> PartialOrder"
by (simp add: P_def fix_subset po_subset_po)

lemma (in Tarski) Y_subset_A: "Y <= A"
apply (rule subset_trans [OF _ fix_subset])
apply (rule Y_ss [simplified P_def])
done

lemma (in Tarski) lubY_in_A: "lub Y cl \<in> A"
by (simp add: Y_subset_A [THEN lub_in_lattice])

lemma (in Tarski) lubY_le_flubY: "(lub Y cl, f (lub Y cl)) \<in> r"
apply (rule lub_least)
apply (rule Y_subset_A)
apply (rule f_in_funcset [THEN funcset_mem])
apply (rule lubY_in_A)
-- {* @{text "Y <= P ==> f x = x"} *}
apply (rule ballI)
apply (rule_tac t = "x" in fix_imp_eq [THEN subst])
apply (erule Y_ss [simplified P_def, THEN subsetD])
-- {* @{text "reduce (f x, f (lub Y cl)) \<in> r to (x, lub Y cl) \<in> r"} by monotonicity *}
apply (rule_tac f = "f" in monotoneE)
apply (rule monotone_f)
apply (simp add: Y_subset_A [THEN subsetD])
apply (rule lubY_in_A)
apply (simp add: lub_upper Y_subset_A)
done

lemma (in Tarski) intY1_subset: "intY1 <= A"
apply (unfold intY1_def)
apply (rule interval_subset)
apply (rule lubY_in_A)
apply (rule Top_in_lattice)
done

lemmas (in Tarski) intY1_elem = intY1_subset [THEN subsetD]

lemma (in Tarski) intY1_f_closed: "x \<in> intY1 \<Longrightarrow> f x \<in> intY1"
apply (simp add: intY1_def  interval_def)
apply (rule conjI)
apply (rule transE)
apply (rule CO_trans)
apply (rule lubY_le_flubY)
-- {* @{text "(f (lub Y cl), f x) \<in> r"} *}
apply (rule_tac f=f in monotoneE)
apply (rule monotone_f)
apply (rule lubY_in_A)
apply (simp add: intY1_def interval_def  intY1_elem)
apply (simp add: intY1_def  interval_def)
-- {* @{text "(f x, Top cl) \<in> r"} *}
apply (rule Top_prop)
apply (rule f_in_funcset [THEN funcset_mem])
apply (simp add: intY1_def interval_def  intY1_elem)
done

lemma (in Tarski) intY1_func: "(%x: intY1. f x) \<in> intY1 -> intY1"
apply (rule restrictI)
apply (erule intY1_f_closed)
done

lemma (in Tarski) intY1_mono:
     "monotone (%x: intY1. f x) intY1 (induced intY1 r)"
apply (auto simp add: monotone_def induced_def intY1_f_closed)
apply (blast intro: intY1_elem monotone_f [THEN monotoneE])
done

lemma (in Tarski) intY1_is_cl:
    "(| pset = intY1, order = induced intY1 r |) \<in> CompleteLattice"
apply (unfold intY1_def)
apply (rule interv_is_compl_latt)
apply (rule lubY_in_A)
apply (rule Top_in_lattice)
apply (rule Top_intv_not_empty)
apply (rule lubY_in_A)
done

lemma (in Tarski) v_in_P: "v \<in> P"
apply (unfold P_def)
apply (rule_tac A = "intY1" in fixf_subset)
apply (rule intY1_subset)
apply (simp add: Tarski.glbH_is_fixp [OF _ intY1_is_cl, simplified]
                 v_def CL_imp_PO intY1_is_cl CLF_def intY1_func intY1_mono)
done

lemma (in Tarski) z_in_interval:
     "[| z \<in> P; \<forall>y\<in>Y. (y, z) \<in> induced P r |] ==> z \<in> intY1"
apply (unfold intY1_def P_def)
apply (rule intervalI)
prefer 2
 apply (erule fix_subset [THEN subsetD, THEN Top_prop])
apply (rule lub_least)
apply (rule Y_subset_A)
apply (fast elim!: fix_subset [THEN subsetD])
apply (simp add: induced_def)
done

lemma (in Tarski) f'z_in_int_rel: "[| z \<in> P; \<forall>y\<in>Y. (y, z) \<in> induced P r |]
      ==> ((%x: intY1. f x) z, z) \<in> induced intY1 r"
apply (simp add: induced_def  intY1_f_closed z_in_interval P_def)
apply (simp add: fix_imp_eq [of _ f A] fix_subset [of f A, THEN subsetD]
                 CO_refl [THEN reflE])
done

lemma (in Tarski) tarski_full_lemma:
     "\<exists>L. isLub Y (| pset = P, order = induced P r |) L"
apply (rule_tac x = "v" in exI)
apply (simp add: isLub_def)
-- {* @{text "v \<in> P"} *}
apply (simp add: v_in_P)
apply (rule conjI)
-- {* @{text v} is lub *}
-- {* @{text "1. \<forall>y:Y. (y, v) \<in> induced P r"} *}
apply (rule ballI)
apply (simp add: induced_def subsetD v_in_P)
apply (rule conjI)
apply (erule Y_ss [THEN subsetD])
apply (rule_tac b = "lub Y cl" in transE)
apply (rule CO_trans)
apply (rule lub_upper)
apply (rule Y_subset_A, assumption)
apply (rule_tac b = "Top cl" in interval_imp_mem)
apply (simp add: v_def)
apply (fold intY1_def)
apply (rule Tarski.glb_in_lattice [OF _ intY1_is_cl, simplified])
 apply (simp add: CL_imp_PO intY1_is_cl, force)
-- {* @{text v} is LEAST ub *}
apply clarify
apply (rule indI)
  prefer 3 apply assumption
 prefer 2 apply (simp add: v_in_P)
apply (unfold v_def)
apply (rule indE)
apply (rule_tac [2] intY1_subset)
apply (rule Tarski.glb_lower [OF _ intY1_is_cl, simplified])
  apply (simp add: CL_imp_PO intY1_is_cl)
 apply force
apply (simp add: induced_def intY1_f_closed z_in_interval)
apply (simp add: P_def fix_imp_eq [of _ f A]
                 fix_subset [of f A, THEN subsetD]
                 CO_refl [THEN reflE])
done

lemma CompleteLatticeI_simp:
     "[| (| pset = A, order = r |) \<in> PartialOrder;
         \<forall>S. S <= A --> (\<exists>L. isLub S (| pset = A, order = r |)  L) |]
    ==> (| pset = A, order = r |) \<in> CompleteLattice"
by (simp add: CompleteLatticeI Rdual)

theorem (in CLF) Tarski_full:
     "(| pset = P, order = induced P r|) \<in> CompleteLattice"
apply (rule CompleteLatticeI_simp)
apply (rule fixf_po, clarify)
apply (simp add: P_def A_def r_def)
apply (blast intro!: Tarski.tarski_full_lemma cl_po cl_co f_cl)
done

end
