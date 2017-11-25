;; Packages

(eval-and-compile
  (add-to-list 'load-path "~/.emacs.d/lisp/company-coq/etc/")
  (add-to-list 'load-path "~/.emacs.d/lisp/company-coq"))

(require 'company)
(require 'dash)
(require 'noflet)
(require 'screenshots)

(my/basic-setup)
(my/faces-setup)

;;; Redefine parts of company

(defmacro company--electric-do (&rest body)
  (declare (indent 0) (debug t))
  `(when (company-manual-begin)
     ,@body))

(defun company-show-doc-buffer ()
  "Temporarily show the documentation buffer for the selection."
  (interactive)
  (let (other-window-scroll-buffer)
    (company--electric-do
      (let* ((selected (nth company-selection company-candidates))
             (doc-buffer (or (company-call-backend 'doc-buffer selected)
                             (error "No documentation available")))
             start)
        (when (consp doc-buffer)
          (setq start (cdr doc-buffer)
                doc-buffer (car doc-buffer)))
        (setq other-window-scroll-buffer (get-buffer doc-buffer))
        (let ((win (display-buffer doc-buffer t)))
          (set-window-start win (if start start (point-min))))))))

(defun company-show-location ()
  "Temporarily display a buffer showing the selected candidate in context."
  (interactive)
  (let (other-window-scroll-buffer)
    (company--electric-do
      (let* ((selected (nth company-selection company-candidates))
             (location (company-call-backend 'location selected))
             (pos (or (cdr location) (error "No location available")))
             (buffer (or (and (bufferp (car location)) (car location))
                         (find-file-noselect (car location) t))))
        (setq other-window-scroll-buffer (get-buffer buffer))
        (with-selected-window (display-buffer buffer t)
          (save-restriction
            (widen)
            (if (bufferp (car location))
                (goto-char pos)
              (goto-char (point-min))
              (forward-line (1- pos))))
          (set-window-start nil (point)))))))

;;; Setup company-coq

(require 'proof-site)

(setq proof-splash-enable nil
      company-coq-disabled-features '(hello spinner)
      company-coq--prettify-abbrevs t)

(put 'company-coq-fold 'disabled nil)

(add-hook 'coq-mode-hook (lambda ()
                           (require 'company-coq)
                           (set-face-attribute 'company-coq-comment-h1-face nil :height 1.5)
                           (set-face-attribute 'company-coq-comment-h2-face nil :height 1.3)
                           (set-face-attribute 'company-coq-comment-h3-face nil :height 1.2)
                           (company-coq-mode)
                           (setq company-idle-delay 0)))

(defvar my/github-width/3   '(0.3333 . 275))
(defvar my/github-width/2   '(0.5    . 420))
(defvar my/github-width*2/3 '(0.6666 . 560))

;; (profiler-start 'cpu)

;;; Screenshots

;;;;;;;;;;;;;;;;
;; CoqPL 2016 ;;
;;;;;;;;;;;;;;;;

;; (set-face-attribute 'default nil :family "Ubuntu Mono" :height 400 :foreground "black" :background "white")
;; (set-fontset-font t 'unicode "Ubuntu Mono")
;; (set-fontset-font t 'unicode "Symbola Monospacified for Ubuntu Mono" nil 'append)

;; (my/with-screenshot '(nil . 1280) 10 nil nil "Context-sensitive autocompletion with holes" "coq-pl-16-autocompletion"
;;   (insert "appin")
;;   (my/send-keys "<C-return>"))

;; (my/with-screenshot '(nil . 1280) 17 nil nil "Offline documentation" "coq-pl-16-documentation"
;;   (insert "appin")
;;   (my/send-keys "<C-return> C-h")
;;   (with-current-buffer company-coq--doc-buffer
;;     (text-scale-decrease 2)))

;; (my/with-screenshot '(nil . 1280) 13 nil nil "Point and click documentation" "coq-pl-16-point-and-click"
;;   (my/start-pg-no-windows)
;;   (my/insert-with-point "<|>plus\n")
;;   (my/send-keys "<menu>"))

;;;;;;;;;;;;;;;;;;;;;;
;; Prettify-symbols ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Without | With

(my/with-screenshot my/github-width/2 6 nil "west" "Prettification of math symbols (disabled)." "prettify-disabled"
  (company-coq-features/prettify-symbols -1)
  (my/insert-with-point "Definition PrettySymbols : (<|>nat -> nat -> Prop) :=
  (fun (n m: nat) =>
     forall p, p <> n -> p >= m -> True \\/ False).")
  (message nil))

(my/with-screenshot my/github-width/2 6 nil "east" "Prettification of math symbols (enabled)." "prettify"
  (my/insert-with-point "Definition PrettySymbols : (<|>nat -> nat -> Prop) :=
  (fun (n1 n2: nat) =>
     forall p, p <> n1 -> p >= n2 -> True \\/ False).")
  (company-coq-features/show-key--echo))

;;;;;;;;;;;;;;;;;;;;;
;; Auto completion ;;
;;;;;;;;;;;;;;;;;;;;;

;; Tactics withs docs | Options with docs

(my/with-screenshot my/github-width/2 18 nil "west" "Auto-completion of tactics, with documentation." "refman-tactics"
  (insert "inve")
  (setq-local company-tooltip-limit 5)
  (split-window-vertically 8)
  (my/send-keys "<C-return> C-h"))

(my/with-screenshot my/github-width/2 18 nil "east" "Auto-completion of commands, with documentation." "refman-commands"
  (insert "SetA")
  (setq-local company-tooltip-limit 5)
  (split-window-vertically 8)
  (my/send-keys "<C-return> C-h"))

;; Local | Modules

(my/with-screenshot my/github-width/2 13 nil "west" "Auto-completion of local definitions." "defun-completion"
  (insert "Theorem MyVeryOwnTheorem : True. Proof. apply I. Qed.
Definition MyVeryOwnDefinition : nat -> Type. Proof. apply (fun _ => nat). Defined.
Lemma MyVeryOwnLemma : 1 + 1 >= 2. Proof. auto. Qed.
Example MyVeryOwnExample : forall p, False -> p. Proof. tauto. Qed.")
  (my/send-keys "C-c C-/ C-c C-/")
  (insert "\n\nMyV")
  (my/send-keys "<C-return>"))

(my/with-screenshot my/github-width/2 13 nil "east" "Auto-completion of module names." "modules-completion"
  (my/start-pg-no-windows)
  (insert "Require Import Co.N.Cy.Abs.")
  (my/send-keys "<C-return>"))

;; Hyps | Search | Unicode

(my/with-screenshot my/github-width/3 16 nil "west" "Auto-completion of hypotheses." "hypotheses-completion"
  (my/start-pg-no-windows)
  (my/insert-with-point "Goal forall (myVar1 myVar2 myVar3: nat), nat.
Proof.
  intros.<|>
  apply my")
  (my/send-keys "C-c <C-return>")
  (my/send-keys "C-x 1 M-> <C-return>"))

(my/with-screenshot my/github-width/3 16 nil "center" "Auto-completion of search results." "search-completion"
  (my/start-pg-no-windows)
  (my/insert-with-point "Require Import NArith.
Import Plus.
Set Printing Width 1000.
SearchPattern (_ + _ = _).<|>
plus_")
  (my/send-keys "C-l C-l C-c <C-return>")
  (delete-other-windows)
  (with-selected-window (split-window-vertically 10)
    (set-window-buffer-start-and-point nil proof-response-buffer 1 1))
  (with-current-buffer proof-response-buffer
    (visual-line-mode -1))
  (my/send-keys "M-> <C-return>"))

(my/with-screenshot my/github-width/3 16 nil "east" "Insertion of Unicode symbols." "math-completion"
  (insert "forall α \\bet")
  (my/send-keys "<C-return>"))

;; Tactic notations | Source view

(my/with-screenshot my/github-width/3 13 nil "west" "Auto-completion of user-defined tactic notations." "ltac-completion"
  (my/start-pg-no-windows)
  (toggle-truncate-lines 1) ;; 55 119
  (message nil)
  (my/insert-with-point "Tactic Notation \"myR\" constr(from)
  \"in\" hyp(hyp) := idtac.

Tactic Notation \"myR\" constr(from)
  \"by\" tactic(tac) := idtac.
<|>
myR")
  (overlay-put (make-overlay 54 60) 'invisible 'outline)
  (overlay-put (make-overlay 119 125) 'invisible 'outline)
  (my/send-keys "C-c <C-return>")
  (my/send-keys "C-x 1 M-< M-> <C-return>")
  (set-window-start nil 1))

(my/with-screenshot my/github-width*2/3 13 nil "east" "Source browser (w/ patch)." "source-view"
  (my/start-pg-no-windows)
  (my/insert-with-point "Require Import Arith.
<|>le")
  (my/send-keys "C-c <C-return>")
  (my/send-keys "C-x 1 M->")
  (split-window-horizontally 26)
  (my/send-keys "<C-return> C-w")
  (with-current-buffer "*company-coq: documentation*"
    (toggle-truncate-lines 1)
    (message nil)))

;;;;;;;;;;;;;;;;;;;
;; PG extensions ;;
;;;;;;;;;;;;;;;;;;;

;; Deprecated | Titles in comments | Inline docs

(my/with-screencast my/github-width/3 13 nil "west" 60 1 "Inline docs (C-Click, M-F12)." "inline-docs"
  (progn
    (my/start-pg-no-windows)
    (company-coq-ask-prover "Set Printing Width 40.")
    (my/insert-with-point "Lemma le_S: forall n m : nat,
 <|>le n m ->
 le n <= (S m).
"))
  (ignore)
  "<menu>")

(my/with-screenshot my/github-width/3 13 nil "center" "Special comments for titles." "titles"
  (progn
    (company-coq-features/smart-subscripts 'off)
    (insert "(***    H1 title    ***)

\(*+     H2 title in a     +*)
\(*+ slightly smaller font +*)

\(*!  H3 title for remarks !*)

\(** *  Coqdoc title       **)
\(** ** Coqdoc subtitle    **)
\(** Documentation comment **)

\(* Regular comment *)"))
  (my/send-keys "M-<")
  (while (re-search-forward "\n\n" nil t)
    (let ((ov (make-overlay (match-beginning 0) (match-end 0))))
      (overlay-put ov 'face '(:height 0.30))))
  (set-window-start nil 1)
  (setq cursor-type nil))

(company-coq-features/smart-subscripts 'on)

(my/with-screenshot my/github-width/3 13 nil "east" "Highlighting of deprecated forms." "deprecated"
  (my/insert-with-point "Set Undo 1.
SearchAbout True.
cutrewrite -> (1 + 1 = 2).
double induction x y.
Save Lemma plus_comm.
assert (x := y).")
  (my/send-keys "M-<")
  (display-local-help t))

;; Error diffs | Documentation of errors

(my/with-screenshot my/github-width/2 16 nil "west" "Diff of unification errors (C-c C-a C-d)." "unification"
  (my/start-pg-no-windows)
  (my/insert-with-point "Inductive Tree {T} :=
| Leaf : T -> Tree
| Branch : Tree -> Tree -> Tree.

Fixpoint MakeLargeTree {A} depth (leaf lastleaf:A) :=
match depth with
| O => Leaf lastleaf
| S n => Branch (MakeLargeTree n leaf leaf) (MakeLargeTree n leaf lastleaf)
end.

Inductive TypedTree : @Tree Type -> Type :=
Tr : forall tr, TypedTree tr.

Eval compute in (MakeLargeTree 7 unit nat).

Lemma inhabited_homogeneous:
forall T n (t: T),
inhabited (TypedTree (@MakeLargeTree Type n T T)).
Proof.
intros; constructor.
induction n; simpl; constructor; eauto.
Qed.

Lemma LargeGoal :
inhabited (TypedTree (@MakeLargeTree Type 1 unit nat)).
Proof.
pose (inhabited_homogeneous unit 1 tt) as pr; simpl in *.
exact pr.")
  (my/send-keys "C-c C-b")
  (delete-window (get-buffer-window proof-goals-buffer))
  (my/send-keys "C-x 1")
  (progn
    (company-coq-diff-unification-error)
    (set-window-buffer-with-search proof-script-buffer "Lemma LargeGoal")
    (with-selected-window (split-window-vertically 6)
      (set-window-buffer-with-search proof-response-buffer "The term")
      (with-selected-window (split-window-vertically 5)
        (set-window-buffer nil "*unification-diff*")
        (message nil)))))

(my/with-screenshot my/github-width/2 16 nil "east" "Documentation of errors (C-c C-a C-e)." "errors-doc"
  (my/start-pg-no-windows)
  (my/insert-with-point "Require Import Omega.
Goal forall n: nat, exists m, n = m.
<|>  intros; omega.")
  (my/send-keys "C-c <C-return>")
  (my/send-keys "C-c C-n")
  (recenter 1)
  (my/send-keys "C-c C-a C-e")
  (my/send-keys "C-x 1")
  (with-selected-window (split-window-vertically 4)
    (set-window-buffer-with-search "*company-coq: documentation*" "omega can")
    (with-selected-window (split-window-vertically 8)
      (with-current-buffer proof-response-buffer
        (set-window-buffer nil (current-buffer))
        (kill-local-variable 'mode-line-format)))))

;; Outlines | Code folding | Go to source
;; TODO: outline could be thinner, leaving space for something else (what?)

(my/with-screenshot my/github-width/3 18 nil "west" "Buffer outlines (C-c C-,)." "outline"
  (insert-file-contents "/usr/local/lib/coq/theories/Arith/Plus.v")
  (rename-buffer "Plus.v")
  (progn
    (my/send-keys "C-c C-,")
    (toggle-truncate-lines 1)
    (let ((inhibit-read-only t))
      (save-excursion
        (goto-char (point-min))
        (while (and (forward-line) (not (eobp)))
          (delete-char 4))))
    (message nil)))

(my/with-screencast my/github-width/3 18 nil "center" 50 1 "Code folding (S-tab, C-c C-/)." "folding"
  (my/insert-with-point "<|>Goal forall a b c d e: Prop,
  a -> b -> c -> d -> e ->
  (a /\\ b) /\\ (c /\\ (d /\\ e)).
Proof.
  split.
  - split.
    + trivial.
    + assumption.
  - split.
    + trivial.
    + { split.
        * assumption.
        * auto. }
Qed.

Goal True -> True.
Proof.
  intros; apply I.
Qed.

Goal False -> True.
Proof.
  intros; assumption.
Qed.")
  "C-u 105 C-f"
  "RET" "RET" "RET"
  "C-u 74 C-f"
  "RET" "RET" "RET"
  "M-<"
  "C-c C-/" "C-c C-/ C-c C-/" "C-c C-\\" "C-c C-\\ C-c C-\\");; HACK due to incorrect last-command

(my/with-screencast my/github-width/3 18 nil "center" 100 0 "Jump to definition (M-.)." "jump-to-definition"
  (progn (my/insert-with-point "Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

<|>Proof.
  exfalso.
  apply inj_pair2_eq_dec in H; trivial.
  apply eq_nat_dec.
Qed.")
         (recenter-top-bottom 0)
         (my/send-keys "C-c <C-return>")
         (proof-shell-wait)
         (delete-other-windows)
         (message nil))
  "C-u 9 C-f"
  (progn (my/send-keys "M-.")
         (toggle-truncate-lines t)
         (message nil)
         (setq last-command 'my/keep-window))
  (setq last-command 'my/keep-window)
  "C-x k"
  "C-u 17 C-f"
  (progn (my/send-keys "M-.")
         (toggle-truncate-lines t)
         (message nil)
         (setq last-command 'my/keep-window))
  (setq last-command 'my/keep-window)
  "C-x k"
  "C-u 40 C-f"
  (progn (my/send-keys "M-.")
         (toggle-truncate-lines t)
         (message nil)
         (setq last-command 'my/keep-window))
  (setq last-command 'my/keep-window)
  "C-x k")

;; Snippets | Match snippets | Smart intros

(my/with-screencast my/github-width/3 13 nil "west" 20 8 "Match snippets (M-RET, C-c C-a RET)." "match-function"
  (my/start-pg-no-windows)

  (:split "Fixpoint nsum l :=") "RET"
  (:split "miw") "<C-return>" "<C-return> RET"
  (:split "l") "TAB" "<M-return>"
  (:split "[]") "TAB" (:split "0") "TAB <M-return>"
  (:split "h :: t") "TAB" (:split "h + nsum t") "M->" "." "RET"

  (:split "Fixpoint nsum' l :=") "RET"
  (:split "match!") "<C-backspace>"
  (:minibuf "Type to destruct (nat, list, …): " "list")
  (progn (company-coq-insert-match-construct "list") (message nil))
  (:split "l") "TAB" (:split "0") "TAB" (:split "x + nsum x0") "M->" ".")

(my/with-screencast my/github-width/3 13 nil "center" 20 8 "Match goal snippets (M-S-RET)." "match-goal"
  (:split "mgw") "<C-return>" "<C-return> RET"
  "<M-S-return>" "TAB" (:split "?a /\\ ?b") "TAB" (:split "?a") "TAB" "RET"
  (:split "destr") "<C-return>" "<C-return> RET" (:split "H; ass") "<C-return>" "<C-return> RET" "M->" ".")

(my/with-screencast my/github-width/3 13 nil "east" 20 8 "Smart intros." "smart-intros"
  (progn
    (my/start-pg-no-windows)
    (insert "Goal forall x y z: nat,
  x >= y -> y >= z -> x >= z.
Proof.
  ")
    (my/send-keys "C-c <C-return>")
    (proof-shell-wait)
    (my/send-keys "C-x 1 M-< M->"))
  (:split "intros!") "<C-return>" "<C-return> RET")

;; Refactorings (TODO: add to README)

(defvar my/ovs nil)

(my/with-screencast my/github-width/2 12 nil "west" 80 2 "Refactoring of [Import]s (right-click, <menu>)" "refactor-imports"
  (progn
    (my/start-pg-no-windows)
    (my/insert-with-point "<|>Require Import
        Setoid
        MSetAVL
        String
        DoubleCyclic.")
    (display-local-help))
  (ignore)
  (message (company-coq-features/refactorings--get-prompt-at-point "\n  "))
  (ignore)
  (save-excursion
    (goto-char (point-at-eol))
    (setq my/ovs (company-coq-features/refactorings--reqs-add-overlays (point-max) t))
    (let ((resize-mini-windows t))
      (message "Apply changes? (y or n) ")))
  (ignore)
  (progn (message "Apply changes? (y or n) y")
         (company-coq-features/refactorings--reqs-commit my/ovs)))

;; Help on prettifications | Help on symbols

(my/with-screenshot my/github-width/2 3 nil "west" "Help with Unicode input in echo area." "unicode-help"
  (my/insert-with-point "Notation \"A <|>∪ B\" := (fun x => A x \\/ B x)\n  (at level 0).")
  (company-coq-features/show-key--echo))

(my/with-screenshot my/github-width/2 3 nil "east" "Details about prettifications in echo area." "prettify-help"
  (my/insert-with-point "Notation \"A ∪ B\" := (<|>fun x => A x \\/ B x)\n  (at level 0).")
  (company-coq-features/show-key--echo))

;; (profiler-report)
(kill-emacs)
