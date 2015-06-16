Require Import Utf8.

(* Global folding should work here *)
Ltac SimpleLtac a b cde := idtac.

(*
(progn
  (setq coq-prog-name "/build/coq-trunk-pr/bin/coqtop")
  (setq coq-prog-args '("-emacs-U" "-coqlib" "/build/coq-trunk-pr/")))
 *)

Goal True = False -> False.
  intros.
  rewrite <- ?H. (* Is this variable properly colored? Ideally it should not be colored at all *)
  apply I.
Qed.

(* This should be underlined. *)
Unset Undo.

(* This should not be underlined *)
Fail abc_Unset Undo.

Inductive AAABBB :=
| AAA1
| AAA2 : BBBCCC -> AAABBB
with BBBCCC :=
     | BBB1
     | BBB2 : AAABBB -> BBBCCC.

(* Are symbols correctly prettified? *)

Definition PrettySymbols : (nat -> nat -> Prop) :=
  (fun (n m: nat) =>
     forall p, p <> n -> p >= m -> True \/ False).

(** Is this comment highlighted differently? Does it properly fill (try pressing M-q (fill-paragraph)) *)

(* AAABBB and BBBCCC should autocomplete without starting the prover, and appear in the outline (C-c C-,) *)

(* Start prover *)
Require Import Omega Coq.Arith.Arith. (* This should autocomplete *)
SearchAbout plus.
(* plu should autocomplete after running this search *)
(* Pressing <menu> on plus should show a definition inline. Same for SimpleLtac *)

Lemma clear_search : True. Proof I.

Fail Fix_F_inv. (* Does the infobox resize properly? *)

(* Does C-w (location) work? Is the point at the beginning of the preceeding comment? *)
Locate le.
Locate gcd.
Locate PrettySymbols.

Goal forall {A} f g (x: A), f = g -> f x -> g x.
Proof.
  intros.
  Hint Extern 1 => subst. (* HintExter should complete *)
  match goal with
  | [ H: ?a |- _ ] => eauto (* Is the variable name highlighted? But not in comments: ?a *)
  end.
  Undo 1.
  congruence.
Qed.

Lemma TestSubscripts :
  forall x: True, True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> nat.
Proof.
  intros.
  (* Are subscripts displaying properly? *)
  constructor.
Qed.

Print TestSubscripts.

Lemma TestLemma : (* This is a template *)
  forall number (hypothesis : number + 1 < number),
    number + 2 < number + 1.
Proof.
  (* intros! Should works here *)
  intros number hypothesis.
  induction number. (* number should be autocompleted here *)
  simpl in *.
  omega. (* Documentation should be available here *)

  simpl in *.
  (* This should be typeable using:
  Require Import C.NA.NA *)
  Require Import Coq.NArith.NArith.

  assert (x := plus_0_r). (* This should be underlined *)

  apply lt_n_S.
  apply lt_S_n in hypothesis.
  intuition. (* Typing C-c C-RET after C-RET should exit  *)

  (* C-x n d here should single this proof out (C-x n w to exit) *)
Qed.

Example NameContaining_with_ : True. (* Dummy Example to add a name containing "with" to the context *)
apply I.
Qed.

Fixpoint TestFixpoint (l: list nat) :=
  (* It should be possible to type "match ... with" and press enter to go to the next line *)
  match l with
  | nil => nil
  | cons h t => cons h (TestCo t)
  end
with TestCo l :=
  match l with
  | nil => nil
  | cons h t => cons h (TestFixpoint t)
  end.

(* TestFixpoin and TestCo should autocomplete here. C-h should show their
types. C-w should work, too *)

(* C-c C-& should lookup symbols *)
(* C-c C-, should show an occur buffer *)

Section TestSectionName.
  Variable A: nat.

  Section OtherSection.
    Hypothesis H: True.

    Lemma t: True -> 1 + 1 = 2.
    Proof.
      intros.
      (* Try lemma-from-goal here *)
    Abort.

  End OtherSection. (* These names should autocomplete *)
End TestSectionName.

Check TestLemma. (* This name should autocomplete *)

Lemma TestLemma2 : False.
Proof.
  cutrewrite -> (False = True). (* This should be inserted with holes. Typing ";RET" should exit the snippet. *)
  apply I.
  replace False with True.
  reflexivity.
Admitted.

(* number and hypothesis shouldn't be available here *)

Let AbortedLemma : False.
  apply TestLemma2. (* This should autocomplete. *)
Abort.

Goal True.
  idtac "!!!" 1.
  idtac "!!!" 2.
  idtac "!!!" 3.
  idtac "!!!" 4.
  auto. (* company-coq-search-in-coq-buffer should show these calls *)
Qed.

(* M-x company-coq-tutorial should work *)

(* Print Instances should show a dropdown when inserted *)

Require Import Utf8.
Lemma MathCompletion : ∀ x, x > 1 → x > 0. (* This can be typed using \forall *)
  intros x H.
  info_auto with arith.
Qed.

Goal True = True.
  (* (company-coq-diff-unification-error) should show diffs for all these errors *)
  Fail apply 1.
  Fail (apply (@eq_refl Type)).
  Set Printing All.
  Fail (apply (@eq_refl Type)).
  Unset Printing All.
  reflexivity.
Qed.

Inductive Tree {T} :=
| Leaf : T -> Tree
| Branch : Tree -> Tree -> Tree.

Fixpoint MakeLargeTree {A} depth (leaf lastleaf:A) :=
  match depth with
  | O => Leaf lastleaf
  | S n => Branch (MakeLargeTree n leaf leaf) (MakeLargeTree n leaf lastleaf)
  end.

Inductive TypedTree : @Tree Type -> Type :=
| TypedLeaf : forall A, A -> TypedTree (Leaf A)
| TypedBranch : forall t1 t2, TypedTree t1 -> TypedTree t2 -> TypedTree (Branch t1 t2).

Eval compute in (MakeLargeTree 7 unit nat).

Lemma inhabited_homogeneous:
  forall T n (t: T),
    inhabited (TypedTree (@MakeLargeTree Type n T T)).
Proof.
  intros; constructor.
  induction n; simpl; constructor; eauto.
Qed.

Set Printing All.

Definition Depth := 5.

Lemma LargeGoal : inhabited (TypedTree (@MakeLargeTree Type Depth unit nat)).
Proof.
  pose proof (inhabited_homogeneous unit Depth tt) as pr.
  simpl in *.

  Fail exact pr.
  (* (company-coq-diff-unification-error) *)
  Unset Printing All.

  (* Position in the goals buffer shouldn't change when thorem names are autocompleted. *)
Admitted.

(** Error messages **)

Fail Require Import NonExistentModule.

Goal True -> True -> True.
  Fail intros a a a.
  Fail intros; intro.
  Fail intro before NonExistent. (* Far at the bottom of the page *)
  Fail exists 1.
  Fail apply False. (* undocumented *)

  Inductive Ind : Type -> Type :=
  | Const : forall {B}, B -> Ind B.

  Fail Check Const (Const nat).

  constructor.
Qed.

Require Import Qcanon.

Lemma test : forall vvvvv, exists vvvvv', vvvvv' > vvvvv.
Proof.
  intros.
  exists (Qcplus vvvvv 1). (* source view should be available here *)

  setoid_rewrite Qclt_minus_iff.
  rewrite Qcplus_comm.
  rewrite Qcplus_assoc.
  ring_simplify.
  reflexivity.
Qed.

(* vvv shouldn't be available here *)

Require Import Omega.

(* Does [zif] yield a list of tactic names? Are they browsable? (C-w) *)

(* Does [Simple] yield a tactic completion? Is it a snippet? Is there a source view feature? *)

Tactic Notation "myR" constr(from) "->" constr(to) "by" tactic(tac) := idtac.
Tactic Notation "myR" constr(from) "->" constr(to) "in" hyp(hyp) "by" tactic(tac) := idtac.

(* Do these notations autocomplete properly? *)

Ltac ABC := idtac.
Fixpoint ABC n :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | _ => 0
  end.

Require Import Bvector.
Require Import DecBool.
Require Import Bool.
Require Import BoolEq.
Require Import Zerob.
Require Import Setoid.
Require Import Utf8.
Require Import Utf8_core.
Require Import Mergesort.
Require Import Reals.
Require Import Sorting.
Require Import Sorted.
Require Import Heap.
Require Import Permutation.
Require Import PermutSetoid.
Require Import PermutEq.
Require Import ZBinary.
Require Import ZSigZAxioms.
Require Import ZSig.
Require Import ZMulOrder.
Require Import ZLcm.
Require Import ZLt.
Require Import ZAxioms.
Require Import ZSgnAbs.
Require Import ZDivEucl.
Require Import ZBase.
Require Import ZDivFloor.
Require Import ZAddOrder.
Require Import ZParity.
Require Import ZProperties.
Require Import ZAdd.
Require Import ZMaxMin.
Require Import ZMul.
Require Import ZGcd.
Require Import ZPow.
Require Import ZBits.
Require Import ZDivTrunc.
Require Import BigZ.
Require Import ZMake.
Require Import ZNatPairs.
Require Import BigNumPrelude.
Require Import ZModulo.
Require Import DoubleSub.
Require Import DoubleMul.
Require Import DoubleType.
Require Import DoubleBase.
Require Import DoubleDivn1.
Require Import DoubleAdd.
Require Import DoubleDiv.
Require Import DoubleCyclic.
Require Import DoubleSqrt.
Require Import DoubleLift.
Require Import Int31.
Require Import Ring31.
Require Import Cyclic31.
Require Import CyclicAxioms.
Require Import NZCyclic.
Require Import BinNums.
Require Import QMake.
Require Import BigQ.
Require Import QSig.
Require Import NumPrelude.
Require Import NaryFunctions.
Require Import NBinary.
Require Import NMake_gen.
Require Import Nbasic.
Require Import BigN.
Require Import NMake.
Require Import NSigNAxioms.
Require Import NSig.
Require Import NPeano.
Require Import NAddOrder.
Require Import NIso.
Require Import NProperties.
Require Import NAdd.
Require Import NOrder.
Require Import NLcm.
Require Import NSqrt.
Require Import NStrongRec.
Require Import NParity.
Require Import NLog.
Require Import NSub.
Require Import NDefOps.
Require Import NBase.
Require Import NPow.
Require Import NMulOrder.
Require Import NMaxMin.
Require Import NBits.
Require Import NGcd.
Require Import NAxioms.
Require Import NDiv.
Require Import NZDiv.
Require Import NZParity.
Require Import NZPow.
Require Import NZProperties.
Require Import NZOrder.
Require Import NZAdd.
Require Import NZGcd.
Require Import NZDomain.
Require Import NZAxioms.
Require Import NZLog.
Require Import NZAddOrder.
Require Import NZMulOrder.
Require Import NZBase.
Require Import NZMul.
Require Import NZBits.
Require Import NZSqrt.
Require Import Pnat.
Require Import BinPosDef.
Require Import BinPos.
Require Import POrderedType.
Require Import PArith.
Require Import Zwf.
Require Import Zcompare.
Require Import Zpower.
Require Import Zmisc.
Require Import Zsqrt_compat.
Require Import Int.
Require Import Zmax.
Require Import Zgcd_alt.
Require Import ZArith.
Require Import auxiliary.
Require Import Zeuclid.
Require Import ZArith_base.
Require Import Zminmax.
Require Import Wf_Z.
Require Import Zpow_alt.
Require Import BinIntDef.
Require Import Zorder.
Require Import Zpow_facts.
Require Import Zbool.
Require Import BinInt.
Require Import Zcomplements.
Require Import Znat.
Require Import Zquot.
Require Import Zdigits.
Require Import Zabs.
Require Import Zmin.
Require Import Zhints.
Require Import ZArith_dec.
Require Import Zpow_def.
Require Import Zeven.
Require Import Zdiv.
Require Import Znumtheory.
Require Import Zlogarithm.
Require Import Arith_base.
Require Import Compare.
Require Import Euclid.
Require Import Gt.
Require Import Compare_dec.
Require Import Wf_nat.
Require Import Min.
Require Import Even.
Require Import Bool_nat.
Require Import Plus.
Require Import Le.
Require Import EqNat.
Require Import Mult.
Require Import Arith.
Require Import Peano_dec.
Require Import Lt.
Require Import Minus.
Require Import Div2.
Require Import Between.
Require Import Max.
Require Import Utils.
Require Import Syntax.
Require Import Program.
Require Import Combinators.
Require Import Tactics.
Require Import Basics.
Require Import Equality.
Require Import Subset.
Require Import Logic.
Require Import Logic_Type.
Require Import Peano.
Require Import Tactics.
Require Import Datatypes.
Require Import Prelude.
Require Import Specif.
Require Import Inclusion.
Require Import Wellfounded.
Require Import Inverse_Image.
Require Import Lexicographic_Product.
Require Import Union.
Require Import Lexicographic_Exponentiation.
Require Import Transitive_Closure.
Require Import Disjoint_Union.
Require Import Well_Ordering.
Require Import FMaps.
Require Import FSetInterface.
Require Import FSets.
Require Import FMapAVL.
Require Import FSetList.
Require Import FMapList.
Require Import FSetWeakList.
Require Import FMapPositive.
Require Import FMapInterface.
Require Import FSetAVL.
Require Import FSetPositive.
Require Import FSetDecide.
Require Import FSetBridge.
Require Import FSetFacts.
Require Import FSetEqProperties.
Require Import FMapWeakList.
Require Import FMapFacts.
Require Import FSetCompat.
Require Import FSetToFiniteSet.
Require Import FMapFullAVL.
Require Import FSetProperties.
Require Import Qfield.
Require Import Qreduction.
Require Import Qround.
Require Import Qminmax.
Require Import Qpower.
Require Import Qreals.
Require Import QArith_base.
Require Import Qcanon.
Require Import Qabs.
Require Import QArith.
Require Import Qring.
Require Import QOrderedType.
Require Import NArith.
Require Import BinNatDef.
Require Import Ndec.
Require Import Ngcd_def.
Require Import BinNat.
Require Import Nsqrt_def.
Require Import Ndiv_def.
Require Import Nnat.
Require Import Ndigits.
Require Import Ndist.
Require Import SetoidList.
Require Import ListTactics.
Require Import Streams.
Require Import List.
Require Import SetoidPermutation.
Require Import ListSet.
Require Import StreamMemo.
Require Import ClassicalDescription.
Require Import Eqdep_dec.
Require Import Decidable.
Require Import Diaconescu.
Require Import Epsilon.
Require Import SetIsType.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import Classical_Pred_Type.
Require Import EqdepFacts.
Require Import Eqdep.
Require Import ClassicalEpsilon.
Require Import JMeq.
Require Import Description.
Require Import Hurkens.
Require Import IndefiniteDescription.
Require Import Berardi.
Require Import Classical_Prop.
Require Import ConstructiveEpsilon.
Require Import ProofIrrelevanceFacts.
Require Import ClassicalChoice.
Require Import RelationalChoice.
Require Import ClassicalFacts.
Require Import ClassicalUniqueChoice.
Require Import Classical.
Require Import ChoiceFacts.
Require Import Finite_sets_facts.
Require Import Relations_2.
Require Import Ensembles.
Require Import Finite_sets.
Require Import Multiset.
Require Import Integers.
Require Import Classical_sets.
Require Import Powerset_Classical_facts.
Require Import Image.
Require Import Constructive_sets.
Require Import Permut.
Require Import Relations_1_facts.
Require Import Cpo.
Require Import Powerset_facts.
Require Import Relations_1.
Require Import Infinite_sets.
Require Import Powerset.
Require Import Partial_Order.
Require Import Relations_3_facts.
Require Import Relations_3.
Require Import Uniset.
Require Import Relations_2_facts.
Require Import String.
Require Import Ascii.
Require Import Cauchy_prod.
Require Import Ranalysis_reg.
Require Import Rpow_def.
Require Import RIneq.
Require Import Rgeom.
Require Import RiemannInt_SF.
Require Import Rbase.
Require Import Rseries.
Require Import Rcomplete.
Require Import Ratan.
Require Import Ranalysis.
Require Import Ranalysis2.
Require Import Rtrigo_reg.
Require Import SeqProp.
Require Import Rsigma.
Require Import Cos_rel.
Require Import Rtrigo1.
Require Import Exp_prop.
Require Import Ranalysis3.
Require Import Ranalysis1.
Require Import Rsqrt_def.
Require Import SeqSeries.
Require Import R_Ifp.
Require Import Rminmax.
Require Import Alembert.
Require Import Rfunctions.
Require Import RiemannInt.
Require Import Rlogic.
Require Import ArithProp.
Require Import Rtopology.
Require Import Machin.
Require Import SplitRmult.
Require Import Binomial.
Require Import Cos_plus.
Require Import Rpower.
Require Import Rbasic_fun.
Require Import NewtonInt.
Require Import Rtrigo_fun.
Require Import SplitAbsolu.
Require Import Reals.
Require Import Rtrigo_calc.
Require Import Rtrigo_def.
Require Import Sqrt_reg.
Require Import ROrderedType.
Require Import PartSum.
Require Import AltSeries.
Require Import R_sqr.
Require Import Ranalysis4.
Require Import Rtrigo_alt.
Require Import R_sqrt.
Require Import MVT.
Require Import DiscrR.
Require Import Integration.
Require Import PSeries_reg.
Require Import Rdefinitions.
Require Import Rlimit.
Require Import Rprod.
Require Import Ranalysis5.
Require Import Rderiv.
Require Import Raxioms.
Require Import Rtrigo.
Require Import RList.
Require Import OrdersEx.
Require Import OrdersLists.
Require Import OrdersFacts.
Require Import DecidableTypeEx.
Require Import EqualitiesFacts.
Require Import OrderedTypeAlt.
Require Import OrdersAlt.
Require Import Equalities.
Require Import OrdersTac.
Require Import Orders.
Require Import DecidableType.
Require Import OrderedType.
Require Import OrderedTypeEx.
Require Import GenericMinMax.
Require Import Operators_Properties.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Relations.
Require Import MSetFacts.
Require Import MSetProperties.
Require Import MSetGenTree.
Require Import MSetDecide.
Require Import MSetList.
Require Import MSetPositive.
Require Import MSetInterface.
Require Import MSetToFiniteSet.
Require Import MSetWeakList.
Require Import MSetAVL.
Require Import MSetEqProperties.
Require Import MSets.
Require Import MSetRBT.
Require Import VectorDef.
Require Import Fin.
Require Import VectorSpec.
Require Import Vector.
Require Import SetoidClass.
Require Import EquivDec.
Require Import SetoidTactics.
Require Import Init.
Require Import Morphisms_Prop.
Require Import SetoidDec.
Require Import Morphisms_Relations.
Require Import Morphisms.
Require Import Equivalence.
Require Import RelationClasses.
Require Import RelationPairs.

(* (setq company-coq-extra-symbols-cmd nil) (setq company-coq-extra-symbols-cmd "SearchAbout -\"_ind\"") *)

(* Loaded 8092 symbols (0.088 seconds) With optimized proof-general search *)
(* Loaded 8092 symbols (0.136 seconds) With plain proof-general search *)
(* Loaded 8092 symbols (0.155 seconds) With optimized proof-general search on battery *)
