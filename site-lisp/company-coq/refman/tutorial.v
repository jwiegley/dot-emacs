(***     Company-Coq     ***)

(*+ A better environment for writing +*)
(*+            Coq proofs            +*)

(*! *************************************************** !*)
(*!        Welcome to this company-coq tutorial!        !*)
(*!        Here's a demo of a few nice features         !*)
(*! *************************************************** !*)

(** First of all, let's ensure that company-coq is running.  Did you add

      (package-initialize)

      ;; Open .v files with Proof-General's coq-mode
      (require 'proof-site "~/.emacs.d/lisp/PG/generic/proof-site")

      ;; Load company-coq when opening Coq files
      (add-hook 'coq-mode-hook #'company-coq-mode)

    to your .emacs?  If not, you can try company-coq temporarily; just type
    ‘M-x company-coq-mode’. *)

(******************************************************************************)

(** Let’s get started!  If you use Emacs ≥ 24.4, the symbols below should be
    prettified, though they appear as ASCII in the source file.  You can disable
    this feature by typing ‘M-x prettify-symbols-mode’.  If the symbols show as
    square boxes instead, you may want to install a good unicode font, such as
    Symbola (see http://git.io/company-coq-fonts for more info, or install
    ‘ttf-ancient-fonts’ on Debian).{% TTY-FONTS-MESSAGE %} *)

Definition PrettySymbols : (nat -> nat -> Prop) :=
  (fun (n m: nat) =>
     forall p, p <> n -> p >= m -> True \/ False).

Ltac MySimpleTactic :=
  match goal with
  | [ H: False |- _ ] => exfalso; assumption
  end.

(* Try typing an arrow ‘->’ here: *) 
(* Note that placing the point on a symbol displays the unprettified equivalent
   in the echo area, too.  Try it here: *) Check nat.

(******************************************************************************)

(** Company-Coq knows most basic Coq tactics.  Typing just a few letters is
    enough to locate a tactic, and pressing RET inserts it.  If a tactic
    contains holes, you can navigate them using TAB. *)

(* Try typing ‘applin RET’ here: *) 
(* Try typing ‘SLD RET’ here: *) 

(******************************************************************************)

(** Not sure what a tactic does?  Type part of its name, and press ‘C-h’. *)

(* Try typing ‘appl C-h’ here: *) 

(******************************************************************************)

(** You can also insert math symbols directly in the source file, using TeX. *)

(* Try typing ‘\opl RET’ here: *) 

(******************************************************************************)

(** It's not always obvious how to insert a symbol. For example, how do you
    input ‘≡’?  What about ‘⋆’, ‘⊙’, or ‘⤨’? *)

(* Put the point on one of the symbols above and look at the echo area. *)

(******************************************************************************)

(** Now for a few interactive features.  You'll want to start the prover. *)

(* Start Coq by pressing ‘C-c C-RET’ here: *) 

(******************************************************************************)

(** Now that Coq is started, company-coq can auto-complete library modules. *)

(* Try typing ‘Require Coq.Z.B’ here: *) 

(******************************************************************************)

(** Completion is smart enough to look for theorems and tactics in the current
    buffer (and with the proper Coq patches, in the whole library).  For example,
    it knows about PrettySymbols and MySimpleTactic. *)

(* Try typing ‘Pretty’ here: *) 

(******************************************************************************)

(** Not only does it know about them; it can print their types and
    definitions. *)

(* Try typing ‘MySimple’ here, and press ‘C-h’ *) 

(** Pressing ‘C-c C-d’ on an indentifier (such as ‘plus’) also works. *)

(******************************************************************************)

(** And if type information is not enough, you can ask company-coq to print the
    definition, from the source, of any symbol for which sources are
    available. *)

(* Try typing ‘Pretty’ and pressing ‘C-w’ here: *) 

(******************************************************************************)

(** In addition to lemmas, tactics, and type definitions from the current
    buffer, company-coq also monitors Coq’s responses for lists of identifiers,
    and adjusts completions accordingly *)

(* Run the following snippet, then try typing ‘plus’ *)
SearchAbout eq.


(******************************************************************************)

(** Your favourite Proof-General commands are still available; company-coq just
    makes them more easily accessible: *)

Lemma Transitive_eq : forall A (x y z: A), x = y -> y = z -> x = z.
Proof.
  (* Start the proof by pressing ‘C-c RET’ here: *) 
  (* Now try typing ‘intros! RET’ here: *) 
Abort.

(******************************************************************************)

(** If you just want a quick peek at a symbol or theorem, though, it’s often
    faster to just C-click the symbol. *)

(* Try clicking the words “le” and “exfalso” below, while holding the ‘Control’
   key down.  Release the mouse button to hide the info box.  This also works
   without a graphic environment; just enable ‘xterm-mouse-mode’ (alternatively,
   you can use the ‘<menu>’ key, or even ‘M-F12’). *)
Fail le.
Fail exfalso.

(******************************************************************************)

(** Company-Coq can show an outline of your proof script; it includes links
    to each definition, theorem, and lemma. *)

(* Try pressing ‘C-c C-,’.  Press ‘q’ to exit the outline buffer. *) 

(******************************************************************************)

(** Company-Coq also adds a few convenient snippets to Proof General, like ‘M-RET’
    and ‘M-S-RET’ to insert additional match cases *)

Ltac BasicTactic :=
  match goal with
  | [ H: ?a /\ ?b |- _ ] => destruct H
  (* Place the point on the empty line before ‘end’, and press ‘M-S-RET’. *)
  (* You can press C-d to remove the contents of a field and move to the next.
     Try to reproduce the line above with as few keystrokes as possible! *)
  
  end.

(******************************************************************************)

(** Confused by an error message?  Company-Coq has documentation for (some) of
    them, auto-extracted from the manual. *)

(* Consider the following attempt at using the [omega] tactic: *)

Require Import Omega.
Lemma refl : forall x, exists (y: nat), x = y.
Proof.
  (* Run the following line and inspect the error message: *)
  Fail omega.

  (* Now press ‘C-c C-a C-e’ (e for *e*rror).  This suggest adding intros: *)
  intros.

  (* Try running omega again: *)
  Fail omega.

  (* Pressing ‘C-c C-a C-e’ again suggests that this wasn’t the right approach
     after all. *)
  eauto.
Qed.

(******************************************************************************)

(** Even if you know what an error means, sometimes it’s hard to parse. *)

(* Evaluate the following block: *)

Inductive Tr {T} := TrL : T -> Tr | TrB : Tr -> Tr -> Tr.
Inductive Tt : @Tr Type -> Type := TtL : forall A, A -> Tt (TrL A) | TtBr : forall t1 t2, Tt t1 -> Tt t2 -> Tt (TrB t1 t2).

Fixpoint MkLarge {A} d (l ll:A) :=
  match d with O => TrL ll | S n => TrB (MkLarge n l l) (MkLarge n l ll) end.

Lemma inH: forall T n (t: T), inhabited (Tt (@MkLarge Type n T T)).
  intros; constructor; induction n; simpl; constructor; eauto. Qed.

Lemma LargeGoal : inhabited (Tt (@MkLarge Type 5 unit nat)).
  pose proof (inH unit 5 tt) as pr; simpl in *.
  Set Printing All.

  (* Run up to this point.  The next command fails, due to a type error: *)
  Fail exact pr.

  (* This message is not very readable, as the two terms are very similar.  It
     would be much nicer with just a diff of the two types.  Company-Coq supports
     this: try it with ‘C-c C-a C-d’.  Type ‘q’ to exit. *)
  
  Unset Printing All.
Abort.

(******************************************************************************)

(** In many cases, you’ll want to extract part of your current goal (say, the
    goal plus a few hypotheses) to a separate lemma.  Lemma extraction does just
    that.  Let’s prove a theorem by induction: *)

Lemma my_plus_comm :
  forall p q r,
    (p < q /\ q < r) -> (p + q < q + r) ->
    (exists s, p + q + r < s) -> forall m n, n + m = m + n.
Proof.
  induction m; intros.
  - simpl.
    rewrite plus_0_r.
    apply eq_refl.
  - (* Evaluate everything up to ‘idtac’ below.  Wouldn’t the proof would look
       nicer if this was a separate lemma? *)
    (* Press ‘C-c C-a C-x’ to automatically extract a lemma from your goal. You
       will be prompted for a name, then for hypotheses to keep in your lemma
       (hint: you only need IHm). Try it on the empty line below: *)
    idtac.
    
Abort.

(** By the way, did you notice the links on the bullets? Try clicking them! (or
    pressing RET on them) **)

(******************************************************************************)

(** That’s it for the core features; good luck with your proofs!  Don’t hesitate
    to submit ideas and patches to https://github.com/cpitclaudel/company-coq/,
    and if you use Coq, Proof-General, and company-coq for your research, please
    consider a citation!

    (* Try using ‘M-x company-coq-cite’ on the line below: *)

*)

(******************************************************************************)

(** Here’s one final tip: with the right settings and a few patches to coqtop
    (available in coq-trunk), company-coq can also autocomplete externally
    defined symbols, tactics, and even tactic notations.  Once the patches are
    installed, you can enable these features by adding the following to your
    .emacs: (setq company-coq-live-on-the-edge t) *)

(* (Symbols) Try typing plu here: *) 

(* (Tactics) Try typing zif here: *) 

(** And if you also installed Coq sources (i.e. if you have .v files in addition
    to .vo files in your installation), then you can press ‘M-.’ on identifiers
    (or ‘C-w’ during completion) to show the original definitions in context. *)

(* (Jumping to source) Try pressing ‘M-.’ on the word ‘plus’: *) plus

(******************************************************************************)

(** Many thanks to Pierre Courtieu for his work on Proof General, and to
    Jonathan Leivent and Jason Gross for their tireless bug reports and
    suggestions! *)

(******************************************************************************)

(** This tutorial is licensed under the Creative Commons Attribution-ShareAlike
    4.0 International License.  To view a copy of this license, visit
    http://creativecommons.org/licenses/by-sa/4.0/. *)
