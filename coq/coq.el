;;; coq.el --- Major mode for Coq proof assistant
;; Copyright (C) 1994-2009 LFCS Edinburgh.
;; Authors: Healfdene Goguen, Pierre Courtieu
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; $Id$


;;; Commentary:
;;
;;; History:

(require 'cl)

(eval-when (compile)
  (require 'proof-utils)
  (require 'proof-shell)
  (require 'span)
  (require 'outline)
  (require 'newcomment)
  (require 'etags)
  (unless (proof-try-require 'smie)
    (defvar smie-indent-basic nil)
    (defvar smie-rules-function nil))     ; smie

  (defvar queueitems nil)       ; dynamic scope in p-s-extend-queue-hook
  (defvar coq-time-commands nil)        ; defpacustom
  (defvar coq-use-editing-holes nil)    ; defpacustom
  (defvar coq-compile-before-require nil)       ; defpacustom
  (defvar coq-confirm-external-compilation nil) ; defpacustom
  (proof-ready-for-assistant 'coq))     ; compile for coq


;; FIXME: making these declarations conditional doesn't work
(declare-function smie-bnf->prec2 "smie")
(declare-function smie-rule-parent-p "smie")
(declare-function smie-default-forward-token "smie")
(declare-function smie-default-backward-token "smie")
(declare-function smie-rule-prev-p "smie")
(declare-function smie-rule-separator "smie")
(declare-function smie-rule-parent "smie")

(require 'proof)
(require 'coq-syntax)                   ; sets coq-prog-name
(require 'coq-local-vars)               ;
(require 'coq-abbrev)                   ; coq specific menu



;; ----- coq-shell configuration options

;;; Code:
;; debugging functions
;; (defun proofstack () (coq-get-span-proofstack (span-at (point) 'type)))
;; End debugging

(defcustom coq-prog-name
  (proof-locate-executable "coqtop" t '("C:/Program Files/Coq/bin"))
   "*Name of program to run as Coq. See `proof-prog-name', set from this. 
On Windows with latest Coq package you might need something like:
   C:/Program Files/Coq/bin/coqtop.opt.exe
instead of just \"coqtop\".
This must be a single program name with no arguments; see `coq-prog-args'
to manually adjust the arguments to the Coq process.
See also `coq-prog-env' to adjust the environment."
   :type 'string
   :group 'coq)

;; coq-prog-args is the user-set list of arguments to pass to Coq process,
;; see 'defpacustom prog-args' in proof-config for documentation.

;; For Coq, this should contain -emacs.
;; -translate will be added automatically to this list if `coq-translate-to-v8'
;; is set.  The list is not altered if the user has set this herself.

(defcustom coq-translate-to-v8 nil
  "Whether to use -translate argument to Coq."
  :type 'boolean
  :group 'coq)

;; Fixes default prog args, this is overridden by file variables
(defun coq-build-prog-args ()
  (setq coq-prog-args
        (append (remove-if (lambda (x) (string-match "-emacs" x)) coq-prog-args)
                '("-emacs-U")
                (if coq-translate-to-v8 " -translate"))))

;; fix it
(unless noninteractive ;; compiling
  (coq-build-prog-args))

(defcustom coq-compiler
  (proof-locate-executable "coqc" t nil)
  "Command to invoke the coq compiler."
  :type 'string
  :group 'coq)

(defcustom coq-dependency-analyzer
  (proof-locate-executable "coqdep" t nil)
  "Command to invoke coqdep."
  :type 'string
  :group 'coq)

(defcustom coq-use-makefile nil
  "Whether to look for a Makefile to attempt to guess the command line.
Set to t if you want this feature."
  :type 'string
  :group 'coq)

;; Command to initialize the Coq Proof Assistant

(defcustom coq-default-undo-limit 200
  "Maximum number of Undo's possible when doing a proof."
  :type 'number
  :group 'coq)

(defconst coq-shell-init-cmd
  (format "Set Undo %s . " coq-default-undo-limit))

(require 'coq-syntax)
;; FIXME: Even if we don't use coq-indent for indentation, we still need it for
;; coq-script-parse-cmdend-forward/backward and coq-find-real-start.
(require 'coq-indent)

(defcustom coq-prog-env nil
  "List of environment settings d to pass to Coq process.
On Windows you might need something like:
  (setq coq-prog-env '(\"HOME=C:\\Program Files\\Coq\\\"))"
  :group 'coq)


;; Command to reset the Coq Proof Assistant
(defconst coq-shell-restart-cmd "Reset Initial.\n ")

(defvar coq-shell-prompt-pattern
  "\\(?:\n\\(?:[^\n\371]+\371\\|<prompt>[^\n]+</prompt>\\)\\)"
  "*The prompt pattern for the inferior shell running coq.")

;; FIXME da: this was disabled (set to nil) -- why?
;; da: 3.5: add experimental
;; am:answer: because of bad interaction
;; with coq -R option.
(defvar coq-shell-cd nil
;;  "Add LoadPath \"%s\"." ;; fixes unadorned Require (if .vo exists).
  "*Command of the inferior process to change the directory.")

(defvar coq-shell-proof-completed-regexp "Subtree\\s-proved!\\|Proof\\s-completed"
  "*Regular expression indicating that the proof has been completed.")

(defvar coq-goal-regexp
  "\\(============================\\)\\|\\(subgoal [0-9]+ is:\\)\n")



(defun get-coq-library-directory ()
  (let ((c (substring (shell-command-to-string "coqtop -where") 0 -1 )))
    (if (string-match c "not found")
	  "/usr/local/lib/coq"
      c)))

(defconst coq-library-directory (get-coq-library-directory)
  "The coq library directory, as reported by \"coqtop -where\".")

(defcustom coq-tags (concat coq-library-directory "/theories/TAGS")
  "The default TAGS table for the Coq library."
  :type 'string
  :group 'coq)

(defconst coq-interrupt-regexp "User Interrupt."
  "Regexp corresponding to an interrupt.")

(defcustom coq-www-home-page "http://coq.inria.fr/"
  "Coq home page URL."
  :type 'string
  :group 'coq)


;;
;; Outline mode
;;

;; FIXME, deal with interacive "Definition"
(defvar coq-outline-regexp
;;  (concat "(\\*\\|"
  (concat "[ ]*" (regexp-opt
	   '(
             "Ltac" "Corr" "Modu" "Sect" "Chap" "Goal" "Definition" "Lemm" "Theo" "Fact" "Rema" "Mutu" "Fixp" "Func") t)))
;;)

(defvar coq-outline-heading-end-regexp "\\.[ \t\n]")

(defvar coq-shell-outline-regexp coq-goal-regexp)
(defvar coq-shell-outline-heading-end-regexp coq-goal-regexp)


(defconst coq-state-preserving-tactics-regexp
  (proof-regexp-alt-list coq-state-preserving-tactics))
(defconst coq-state-changing-commands-regexp
  (proof-regexp-alt-list coq-keywords-state-changing-commands))
(defconst coq-state-preserving-commands-regexp
  (proof-regexp-alt-list coq-keywords-state-preserving-commands))
(defconst coq-commands-regexp
  (proof-regexp-alt-list coq-keywords-commands))
(defvar coq-retractable-instruct-regexp
  (proof-regexp-alt-list coq-retractable-instruct))
(defvar coq-non-retractable-instruct-regexp
  (proof-regexp-alt-list coq-non-retractable-instruct))


;;
;; Derived modes
;;

(eval-and-compile
  (define-derived-mode coq-shell-mode proof-shell-mode
    "Coq Shell" nil
    (coq-shell-mode-config)))

(eval-and-compile
  (define-derived-mode coq-response-mode proof-response-mode
  "Coq Response" nil
    (coq-response-config)))

(eval-and-compile
  (define-derived-mode coq-mode proof-mode "Coq"
    "Major mode for Coq scripts.

\\{coq-mode-map}"
    (coq-mode-config)))

(eval-and-compile
  (define-derived-mode coq-goals-mode proof-goals-mode
    "Coq Goals" nil
    (coq-goals-mode-config)))

;; Indentation and navigation support via SMIE.

(defcustom coq-use-smie nil
  "If non-nil, Coq mode will try to use SMIE for indentation.
SMIE is a navigation and indentation framework available in Emacs >= 23.3."
  :type 'boolean
  :group 'coq)

(require 'smie nil 'noerror)

(defconst coq-smie-grammar
  ;; FIXME: This does not cover the tactic scripts.
  ;; FIXME: This only covers a subset of the language.
  ;; FIXME: This does not know about Notations.
  (when (fboundp 'smie-prec2->grammar)
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((exp ("match" matchexp "with" branches "end")
           ("let" assigns "in" exp)
           ("fun" exp "=>" exp)
           ("if" exp "then" exp "else" exp)
           ("forall" exp "," exp)
           ("(" exps ")")
           ("{|" exps "|}")
           (exp ":" exp)
           (exp "->" exp))
      ;; Having "return" here rather than as a separate rule in `exp'
      ;; causes it to be indented at a different level than "with".
      (matchexp (matchexp "return" exp) (exp "in" exp) (exp "as" exp))
      (branches (exp "=>" exp) (branches "|" branches))
      (assigns (exp ":=" exp) (assigns ";" assigns))
      (exps (exp) (exps "," exps))
      (subtactics (tactics "|" tactics))
      (tactics (tactics ";" tactics) ("[" subtactics "]"))
      (cmds ("Lemma" exp ":=" exp)
            ("Definition" exp ":=" exp)
            ("Let" exp ":=" exp)
            ("Function" exp ":=" exp)
            ("Fixpoint" exp ":=" exp)
            ("Inductive" exp ":= inductive" branches)
            ("CoInductive" exp ":= inductive" branches)
            ("Notation" exp ":=" exp)
            ("Record" exp ":=" exp)
            (tactics)
            ;; The above elements are far from the only ones terminated by "."
            ;; (think of all the tactics).  So we won't list them all, instead
            ;; we'll use "." as separator rather than terminator.
            ;; This has the downside that smie-forward-sexp on a "Definition"
            ;; stops right before the "." rather than right after.
            (cmds "." cmds)
            ;; The elements below are trying to capture the syntactic structure
            ;; layered above the commands language.
            ("BeginSubproof" cmds "EndSubproof")
            ("Proof" cmds "Proof End")
            ("Module" cmds "End")
            ("Section" cmds "End")))
    ;; Resolve the "trailing expression ambiguity" as in "else x -> b".
    '((nonassoc "else" "in" "=>" ",") (left ":") (assoc "->"))
    ;; Declare that we don't care about associativity of separators.
    '((assoc "|")) '((assoc ",")) '((assoc ";")) '((assoc ".")))))
  "Parsing table for Coq.  See `smie-grammar'.")

(defun coq-smie-search-token-forward (tokens &optional end)
  "Search for one of TOKENS between point and END."
  (unless end (setq end (point-max)))
  (condition-case nil
      (catch 'found
        (while (< (point) end)
          ;; The default lexer is faster and is good enough for our needs.
          (let ((next (smie-default-forward-token)))
            (cond
             ((zerop (length next)) (forward-sexp 1))
             ((member next tokens) (throw 'found next))))))
    (scan-error nil)))

(defun coq-smie-search-token-backward (tokens &optional end)
  "Search for one of TOKENS between point and END."
  (unless end (setq end (point-min)))
  (condition-case nil
      (catch 'found
        (while (> (point) end)
          ;; The default lexer is faster and is good enough for our needs.
          (let ((next (smie-default-backward-token)))
            (cond
             ((zerop (length next)) (forward-sexp -1))
             ((member next tokens) (throw 'found next))))))
    (scan-error nil)))

;; Lexer.
;; - We distinguish ":=" from ":= inductive" to avoid the circular precedence
;;   constraint ":= < | < ; < :=" where ":= < |" is due to Inductive
;;   definitions, "| < ;" is due to tactics precedence, "; < :=" is due to
;;   "let x:=3; y:=4 in...".
;; - We distinguish the ".-selector" from the terminator "." for
;;   obvious reasons.
;; - We distinguish the "Module M." from "Module M := exp." since the first
;;   opens a new scope (closed by End) whereas the other doesn't.
;; - We drop "Program" because it's easier to consider "Program Function"
;;   as a single token (which behaves like "Function" w.r.t indentation and
;;   parsing) than to get the parser to handle it correctly.

(defconst coq-smie-proof-end-tokens
  ;; '("Qed" "Save" "Defined" "Admitted" "Abort")
  (remove "End" coq-keywords-save-strict))

(defun coq-smie-forward-token ()
  (let ((tok (smie-default-forward-token)))
    (cond
     ((equal tok ".")
      ;; Distinguish field-selector "." from terminator ".".
      (if (or (looking-at "(")                ;Record selector.
              (and (looking-at "[[:alpha:]]") ;Maybe qualified id.
                   (save-excursion
                     (goto-char (1- (point)))
                     (skip-syntax-backward "w_")
                     (looking-at "[[:upper:]]"))))
          ".-selector" "."))
     ((equal tok "Program")
      (let ((pos (point))
            (next (smie-default-forward-token)))
        (if (member next '("Fixpoint" "Declaration" "Lemma"))
            next
          (goto-char pos)
          tok)))
     ((equal tok "Module")
      (let ((pos (point))
            (next (smie-default-forward-token)))
        (unless (equal next "Type") (goto-char pos))
        (save-excursion
          (if (equal (coq-smie-search-token-forward '(":=" ".")) ":=")
              "Module def" tok))))
     ((and (equal tok "") (looking-at "{|")) (goto-char (match-end 0)) "{|")
     ((and (equal tok "|") (eq (char-after) ?\}))
      (goto-char (1+ (point))) "|}")
     ((and (equal tok ":=")
           (save-excursion
             (member (coq-smie-search-token-backward
                      '("let" "Inductive" "Coinductive" "."))
                     '("Inductive" "CoInductive"))))
      ":= inductive")
     ((member tok coq-smie-proof-end-tokens) "Proof End")
     ((member tok '("Proof" "Obligation")) "Proof")
     ((equal tok "Next")
      (let ((pos (point))
            (next (smie-default-forward-token)))
        (if (equal next "Obligation")
            next
          (goto-char pos)
          tok)))
     (tok))))

(defun coq-smie-backward-token ()
  (let ((tok (smie-default-backward-token)))
    (cond
     ((equal tok ".")
      ;; Distinguish field-selector "." from terminator ".".
      (if (or (looking-at "\\.(")             ;Record selector.
              (and (looking-at "\\.[[:alpha:]]") ;Maybe qualified id.
                   (save-excursion
                     (skip-syntax-backward "w_")
                     (looking-at "[[:upper:]]"))))
          ".-selector" "."))
     ((member tok '("Fixpoint" "Declaration" "Lemma"))
      (let ((pos (point))
            (prev (smie-default-backward-token)))
        (unless (equal prev "Program") (goto-char pos))
        tok))
     ((equal tok "Type")
      (let ((pos (point))
            (prev (smie-default-backward-token)))
        (if (equal prev "Module")
            prev
          (goto-char pos)
          tok)))
     ((equal tok "Module")
      (save-excursion
        (if (equal (coq-smie-search-token-forward '(":=" ".")) ":=")
            "Module def" tok)))
     ((and (equal tok "|") (eq (char-before) ?\{))
      (goto-char (1- (point))) "{|")
     ((and (equal tok "") (looking-back "|}" (- (point) 2)))
      (goto-char (match-beginning 0)) "|}")
     ((and (equal tok ":=")
           (save-excursion
             (member (coq-smie-search-token-backward
                      '("let" "Inductive" "Coinductive" "."))
                     '("Inductive" "CoInductive"))))
      ":= inductive")
     ((member tok coq-smie-proof-end-tokens) "Proof End")
     ((equal tok "Obligation")
      (let ((pos (point))
            (prev (smie-default-backward-token)))
        (unless (equal prev "Next") (goto-char pos))
        "Proof"))
     (tok))))

(defun coq-smie-rules (kind token)
  "Indentation rules for Coq.  See `smie-rules-function'.
KIND is the situation and TOKEN is the thing w.r.t which the rule applies."
  (case kind
    (:elem (case token
             (basic proof-indent)))
    (:list-intro
     (or (member token '("fun" "forall"))
         ;; We include "." in list-intro for the ". { .. } \n { .. }" so the
         ;; second {..} is aligned with the first rather than being indented as
         ;; if it were an argument to the first.
         (when (equal token ".")
           (smie-default-forward-token)
           (forward-comment (point-max))
           (looking-at "{"))))
    (:after
     (cond
      ;; Override the default indent step added because of their presence
      ;; in smie-closer-alist.
      ((equal token "with") 4)
      ((and (equal token ";") (smie-rule-parent-p "." "|")) 2)
      ((member token '("," ":=")) 0)))
    (:before
     (cond
      ((equal token "return") (if (smie-rule-parent-p "match") 3))
      ((equal token "|")
       (if (smie-rule-prev-p "with")
           (- (funcall smie-rules-function :after "with") 2)
         (smie-rule-separator kind)))
      ((equal token ":=")
       (if (smie-rule-parent-p "Definition" "Lemma" "Fixpoint" "Inductive"
                               "Function" "Let" "Record")
           (or proof-indent smie-indent-basic)))
      ((equal token ".")
       (if (smie-rule-parent-p "BeginSubproof" "Module" "Section" "Proof") 2))
      ((and (equal token "{") (smie-rule-prev-p ":="))
       (smie-rule-parent))
      ((and (equal token ",") (smie-rule-parent-p "forall")) 2)
      ((and (equal token ":") (smie-rule-parent-p "Lemma")) 2)
      ((and (equal token "Proof End")
            (smie-rule-parent-p "Module" "Section"))
       ;; ¡¡Major gross hack!!
       ;; This typically happens when a Lemma had no "Proof" keyword.
       ;; We should ideally find some other way to handle it (e.g. matching Qed
       ;; not with Proof but with any of the keywords like Lemma that can
       ;; start a new proof), but we can workaround the problem here, because
       ;; SMIE happened to decide arbitrarily that Qed will stop before Module
       ;; when parsing backward.
       ;; FIXME: This is fundamentally very wrong, but it seems to work
       ;; OK in practice.
       (smie-rule-parent 2))
      ((and (equal token "forall") (smie-rule-prev-p ":")
            (smie-rule-parent-p "Lemma"))
       (smie-rule-parent))
      ))))

;;
;; Auxiliary code for Coq modes
;;



;;;;;;;;;;; Trying to accept { and } as terminator for empty commands. Actually
;;;;;;;;;;; I am experimenting two new commands "{" and "}" (without no
;;;;;;;;;;; trailing ".") which behave like BeginSubProof and EndSubproof. The
;;;;;;;;;;; absence of a trailing "." makes it difficult to distinguish between
;;;;;;;;;;; "{" of normal coq code (implicits, records) and this the new
;;;;;;;;;;; commands. We therefore define a coq-script-parse-function to this
;;;;;;;;;;; purpose.

;; coq-end-command-regexp is ni coq-indent.el
(defconst coq-script-command-end-regexp coq-end-command-regexp)
;;        "\\(?:[^.]\\|\\(?:\\.\\.\\)\\)\\.\\(\\s-\\|\\'\\)")



;; slight modification of proof-script-generic-parse-cmdend (one of the
;; candidate for proof-script-parse-function), to allow "{" and "}" to be
;; command terminator when the command is empty. TO PLUG: swith the comment
;; below and rename coq-script-parse-function2 into coq-script-parse-function
(defun coq-script-parse-function ()
  "For `proof-script-parse-function' if `proof-script-command-end-regexp' set."
  (coq-script-parse-cmdend-forward))

;;;;;;;;;;;;;;;;;;;;;;;;;; End of "{" and "} experiments ;;;;;;;;;;;;


(defun coq-set-undo-limit (undos)
  (proof-shell-invisible-command (format "Set Undo %s . " undos)))

;; make this non recursive?
(defun build-list-id-from-string (s)
  "Build a list of string from a string S of the form \"id1|id2|...|idn\"."
  (if (or (not s) (string= s "")) '()
    (let ((x (string-match (concat "\\(" coq-id-shy "\\)\\(?:|\\|\\'\\)\\(.*\\)") s)))
      (if (not x) (error "Cannot extract list of ids from string")
        (cons (match-string 1 s)
              (build-list-id-from-string (match-string 2 s))
              )))
    )
  )

;; Use the statenumber inside the coq prompt to backtrack more easily
(defun coq-last-prompt-info (s)
  "Extract info from the coq prompt S.  See `coq-last-prompt-info-safe'."
  (let ((lastprompt (or s (error "No prompt !!?")))
        (regex
         (concat "\\(" coq-id-shy "\\) < \\([0-9]+\\) |\\(\\(?:" coq-id-shy
                 "|?\\)*\\)| \\([0-9]+\\) < ")))
    (when (string-match regex lastprompt)
      (list (string-to-number (match-string 2 lastprompt))
            (string-to-number (match-string 4 lastprompt))
            (build-list-id-from-string (match-string 3 lastprompt))))))


(defun coq-last-prompt-info-safe ()
  "Return a list with all informations from the last prompt.
The list contains the state number, the proof stack depth, and the names of all
pending proofs (in a list)."
  (coq-last-prompt-info proof-shell-last-prompt))

(defvar coq-last-but-one-statenum 1
  "The state number we want to put in a span.
This is the prompt number given *just before* the command was sent.
This variable remembers this number and will be updated when
used see coq-set-state-number.
Initially 1 because Coq initial state has number 1.")

(defvar coq-last-but-one-proofnum 1
  "As for `coq-last-but-one-statenum' but for stack depth.")

(defvar coq-last-but-one-proofstack '()
  "As for `coq-last-but-one-statenum' but for proof stack symbols.")

(defsubst coq-get-span-statenum (span)
  "Return the state number of the SPAN."
  (span-property span 'statenum))

(defsubst coq-get-span-proofnum (span)
  "Return the proof number of the SPAN."
  (span-property span 'proofnum))

(defsubst coq-get-span-proofstack (span)
  "Return the proof stack (names of pending proofs) of the SPAN."
  (span-property span 'proofstack))

(defsubst coq-set-span-statenum (span val)
  "Set the state number of the SPAN to VAL."
  (span-set-property span 'statenum val))

(defsubst coq-get-span-goalcmd (span)
  "Return the 'goalcmd flag of the SPAN."
  (span-property span 'goalcmd))

(defsubst coq-set-span-goalcmd (span val)
  "Set the 'goalcmd flag of the SPAN to VAL."
  (span-set-property span 'goalcmd val))

(defsubst coq-set-span-proofnum (span val)
  "Set the proof number of the SPAN to VAL."
  (span-set-property span 'proofnum val))

(defsubst coq-set-span-proofstack (span val)
  "Set the proof stack (names of pending proofs) of the SPAN to VAL."
  (span-set-property span 'proofstack val))

(defsubst proof-last-locked-span ()
  (with-current-buffer proof-script-buffer
    (span-at (- (proof-unprocessed-begin) 1) 'type)))

(defun proof-clone-buffer (s &optional erase)
  (let ((nb (get-buffer-create s)))
    (save-window-excursion
      (switch-to-buffer nb)
      (goto-char (point-min))
      (insert "\n************************************\n")
      (goto-char (point-min)))
    (if erase (copy-to-buffer nb (point-min) (point-max))
      (append-to-buffer nb (point-min) (point-max)))
    ;; (set-window-point window pos)
    nb))

;; copy the content of proof-response-buffer into the "response-freeze" buffer,
;; resetting its content if ERASE non nil.
(defun proof-store-buffer-win (buffer &optional erase)
  (proof-with-current-buffer-if-exists buffer
    (let ((newbuffer nil))
      (set-buffer buffer)
      (setq newbuffer (proof-clone-buffer "*response-freeze*" erase))
      (let ((win (display-buffer-other-frame newbuffer))
            (win-point-min (save-window-excursion
                             (switch-to-buffer-other-frame newbuffer)
                             (point-min))))
      (set-window-point win win-point-min)))))

(defun proof-store-response-win (&optional erase)
  (interactive "P")
  (proof-store-buffer-win proof-response-buffer erase))

(defun proof-store-goals-win (&optional erase)
  (interactive "P")
  (proof-store-buffer-win proof-goals-buffer erase))

;; Each time the state changes (hook below), (try to) put the state number in
;; the last locked span (will fail if there is already a number which should
;; happen when going back in the script).  The state number we put is not the
;; last one because the last one has been sent by Coq *after* the change. We
;; use `coq-last-but-one-statenum' instead and then update it.

;;TODO update docstring and comment

(defun coq-set-state-infos ()
  "Set the last locked span's state number to the number found last time.
This number is in the *last but one* prompt (variable `coq-last-but-one-statenum').
If locked span already has a state number, then do nothing. Also updates
`coq-last-but-one-statenum' to the last state number for next time."
  (if proof-shell-last-prompt
      ;; da: did test proof-script-buffer here, but that seems wrong
      ;; since restart needs to reset these values.
      ;; infos = promt infos of the very last prompt
      ;; sp = last locked span, which we want to fill with prompt infos
      (let ((sp    (if proof-script-buffer (proof-last-locked-span)))
            (infos (or (coq-last-prompt-info-safe) '(0 0 nil))))
        (unless (or (not sp) (coq-get-span-statenum sp))
          (coq-set-span-statenum sp coq-last-but-one-statenum))
        (setq coq-last-but-one-statenum (car infos))
        ;; set goalcmd property if this is a goal start
        ;; (ie proofstack has changed and not a save cmd)
        (unless
            (or (not sp) (equal (span-property sp 'type) 'goalsave)
                (<= (length (car (cdr (cdr infos))))
                    (length coq-last-but-one-proofstack)))
          (coq-set-span-goalcmd sp t))
        ;; testing proofstack=nil is not good here because nil is the empty list OR
        ;; the no value, so we test proofnum as it is always set at the same time.
        ;; This is why this test is done before the next one (which sets proofnum)
        (unless (or (not sp) (coq-get-span-proofnum sp))
          (coq-set-span-proofstack sp coq-last-but-one-proofstack))
        (setq coq-last-but-one-proofstack (car (cdr (cdr infos))))
        (unless (or (not sp) (coq-get-span-proofnum sp))
          (coq-set-span-proofnum sp coq-last-but-one-proofnum))
        (setq coq-last-but-one-proofnum (car (cdr infos))))))

;; This hook seems the one we want.
;; WARNING! It is applied once after each command PLUS once before a group of
;; commands is started
(add-hook 'proof-state-change-hook 'coq-set-state-infos)


(defun count-not-intersection (l notin)
  "Return the number of elts of L that are not in NOTIN."
  (let ((l1 l) (l2 notin) (res 0))
    (while l1
      (if (member (car l1) l2) ()
        (setq res (+ res 1))) ; else
      (setq l1 (cdr l1)))
    res
    ))

;; Simplified version of backtracking which uses state numbers, proof stack depth and
;; pending proofs put inside the coq (> v8.1) prompt. It uses the new coq command
;; "Backtrack". The prompt is like this:
;;      state                        proof stack
;;      num                           depth
;;       __                              _
;; aux < 12 |aux|SmallStepAntiReflexive| 4 < \371
;; ^^^^^^   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^     ^
;; usual           pending proofs           usual
;;                                          special char
;; exemple:
;; to go (back) from 12 |lema1|lema2...|leman| xx
;; to                8  |lemb1|lemb2...|lembm| 5
;; we must do "Backtrack 8 5 naborts"
;; where naborts is the number of lemais that are not lembis

;; Rem: We could deal with suspend and resume with more work. We would need a new coq
;; command, because it is better to backtrack with *one* command (because
;; proof-change-hook used above is not exactly called at right times).

(defun coq-find-and-forget (span)
  "Backtrack to SPAN.  Using the \"Backtrack n m p\" coq command."
  (if (eq (span-property span 'type) 'proverproc)
      ;; processed externally (i.e. Require, etc), nothing to do
      ;; (should really be unlocked when we undo the Require).
      nil
  (let* (ans (naborts 0) (nundos 0)
             (proofdepth (coq-get-span-proofnum span))
             (proofstack (coq-get-span-proofstack span))
             (span-staten (coq-get-span-statenum span))
             (naborts (count-not-intersection
                       coq-last-but-one-proofstack proofstack)))
    ;; if we move outside of any proof, coq does not print anything, so clean
    ;; the goals buffer otherwise the old one will still be displayed
    (if (= proofdepth 0) (proof-clean-buffer proof-goals-buffer))
    (unless (and
             ;; return nil (was proof-no-command) in this case:
             ;; this is more efficient as backtrack x y z may be slow
             (equal coq-last-but-one-proofstack proofstack)
             (= coq-last-but-one-proofnum proofdepth)
             (= coq-last-but-one-statenum span-staten))
      (list
       (format "Backtrack %s %s %s . "
               (int-to-string span-staten)
               (int-to-string proofdepth)
               naborts))))))

(defvar coq-current-goal 1
  "Last goal that Emacs looked at.")

(defun coq-goal-hyp ()
  (cond
   ((looking-at "============================\n")
    (goto-char (match-end 0))
    (cons 'goal (int-to-string coq-current-goal)))
   ((looking-at "subgoal \\([0-9]+\\) is:\n")
    (goto-char (match-end 0))
    (cons 'goal (match-string 1))       ;FIXME: This is dead-code!?  --Stef
    (setq coq-current-goal (string-to-number (match-string 1))))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))

(defun coq-state-preserving-p (cmd)
  ;; (or
   (proof-string-match coq-non-retractable-instruct-regexp cmd))
  ;; (and
  ;;  (not (proof-string-match coq-retractable-instruct-regexp cmd))
  ;;  (or
  ;;   (message "Unknown command, hopes this won't desynchronize ProofGeneral")
  ;;   t))))


;;
;; Commands for Coq
;;

(defconst notation-print-kinds-table
  '(("Print Scope(s)" 0) ("Print Visibility" 1))
  "Enumerates the different kinds of notation information one can ask to coq.")

(defun coq-PrintScope ()
  "Show information on notations. Coq specific."
  (interactive)
  (let*
      ((mods
        (completing-read "Infos on notation (TAB to see list): "
                         notation-print-kinds-table))
       (s (read-string  "Name (empty for all): "))
       (all (string-equal s "")))
    (cond
     ((and (string-equal mods "Print Scope(s)") (string-equal s ""))
      (proof-shell-invisible-command (format "Print Scopes.")))
     (t
      (proof-shell-invisible-command (format "%s %s ." mods s)))
     )
    )
  )

(defun coq-guess-or-ask-for-string (s &optional dontguess)
  (let ((guess
         (cond
          (dontguess nil)
          ((use-region-p)
           (buffer-substring-no-properties (region-beginning) (region-end)))
          ((fboundp 'symbol-near-point) (symbol-near-point))
          ((fboundp 'symbol-at-point) (symbol-at-point)))))
    (if (and guess (symbolp guess)) (setq guess (symbol-name guess)))
    (read-string
     (if guess (concat s " (default " guess "): ") (concat s ": "))
     nil 'proof-minibuffer-history guess)))


(defun coq-ask-do (ask do &optional dontguess postformatcmd)
  "Ask for an ident and print the corresponding term."
  (let* ((cmd) (postform (if (eq postformatcmd nil) 'identity postformatcmd)))
    (proof-shell-ready-prover)
    (setq cmd (coq-guess-or-ask-for-string ask dontguess))
    (proof-shell-invisible-command
     (format (concat do " %s . ") (funcall postform cmd))))
  )

(defsubst coq-put-into-brackets (s)
  (concat "[ " s " ]"))

(defsubst coq-put-into-quotes (s)
  (concat "\"" s "\""))

(defun coq-SearchIsos ()
  "Search a term whose type is isomorphic to given type.
This is specific to `coq-mode'."
  (interactive)
  (coq-ask-do
   "SearchPattern (parenthesis mandatory), ex: (?X1 + _ = _ + ?X1)"
   "SearchPattern" nil))

(defun coq-SearchConstant ()
  (interactive)
  (coq-ask-do "Search constant" "Search" nil))

(defun coq-Searchregexp ()
  (interactive)
  (coq-ask-do
   "Search regexp (ex: \"eq_\" nat)"
   "SearchAbout" nil 'coq-put-into-brackets))

(defun coq-SearchRewrite ()
  (interactive)
  (coq-ask-do "SearchRewrite" "SearchRewrite" nil))

(defun coq-SearchAbout ()
  (interactive)
  (coq-ask-do
   "SearchAbout (ex: \"eq_\" eq -bool)"
   "SearchAbout" nil 'coq-put-into-brackets))

(defun coq-Print ()
  "Ask for an ident and print the corresponding term."
  (interactive)
  (coq-ask-do "Print" "Print"))

(defun coq-About ()
  "Ask for an ident and print information on it."
  (interactive)
  (coq-ask-do "About" "About"))

(defun coq-LocateConstant ()
  "Locate a constant."
  (interactive)
  (coq-ask-do "Locate" "Locate"))

(defun coq-LocateLibrary ()
  "Locate a library."
  (interactive)
  (coq-ask-do "Locate Library" "Locate Library"))

(defun coq-LocateNotation ()
  "Locate a notation.  Put it automatically into quotes.
This is specific to `coq-mode'."
  (interactive)
  (coq-ask-do
   "Locate notation (ex: \'exists\' _ , _)" "Locate"
   t 'coq-put-into-quotes))

(defun coq-Pwd ()
  "Display the current Coq working directory."
  (interactive)
  (proof-shell-invisible-command "Pwd."))

(defun coq-Inspect ()
  (interactive)
  (coq-ask-do "Inspect how many objects back?" "Inspect" t))

(defun coq-PrintSection()
  (interactive)
  (coq-ask-do "Print Section" "Print Section" t))

(defun coq-Print-implicit ()
  "Ask for an ident and print the corresponding term."
  (interactive)
  (coq-ask-do "Print Implicit" "Print Implicit"))

(defun coq-Check ()
  "Ask for a term and print its type."
  (interactive)
  (coq-ask-do "Check" "Check"))

(defun coq-Show ()
  "Ask for a number i and show the ith goal."
  (interactive)
  (coq-ask-do "Show goal number" "Show" t))


(proof-definvisible coq-PrintHint "Print Hint. ")

;; Items on show menu
(proof-definvisible coq-show-tree "Show Tree.")
(proof-definvisible coq-show-proof "Show Proof.")
(proof-definvisible coq-show-conjectures "Show Conjectures.")
(proof-definvisible coq-show-intros "Show Intros.") ; see coq-insert-intros below

(defun coq-Compile ()
  "Compiles current buffer."
  (interactive)
  (let* ((n (buffer-name))
	 (l (string-match ".v" n)))
    (compile (concat "make " (substring n 0 l) ".vo"))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;    To guess the command line options   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-guess-command-line (filename)
  "Guess the right command line options to compile FILENAME using `make -n'."
  (if (local-variable-p 'coq-prog-name (current-buffer))
      coq-prog-name
    (let* ((dir (or (file-name-directory filename) "."))
           (makedir
           (cond
            ((file-exists-p (concat dir "Makefile")) ".")
            ;; ((file-exists-p (concat dir "../Makefile")) "..")
            ;; ((file-exists-p (concat dir "../../Makefile")) "../..")
            (t nil))))
      (if (and coq-use-makefile makedir)
          (let*
              ;;TODO, add dir name when makefile is in .. or ../..
              ;;
              ;; da: FIXME: this code causes problems if the make
              ;; command fails.  It should not be used by default
              ;; and should be made more robust.
              ;;
              ((compiled-file (concat (substring
                                       filename 0
                                       (string-match ".v$" filename)) ".vo"))
               (command (shell-command-to-string
                         (concat  "cd " dir ";"
                                  "make -n -W " filename " " compiled-file
                                  "| sed s/coqc/coqtop/"))))
            (message command)
            (setq coq-prog-args nil)
            (concat
             (substring command 0 (string-match " [^ ]*$" command))
             "-emacs-U"))
        coq-prog-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Holes mode switch

(defpacustom use-editing-holes t
  "Enable holes for editing."
  :type 'boolean)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-mode-config ()
  ;; Coq error messages are thrown off by TAB chars.
  (set (make-local-variable 'indent-tabs-mode) nil)
  (setq proof-terminal-string ".")
  (setq proof-script-command-end-regexp coq-script-command-end-regexp)
  (setq proof-script-parse-function 'coq-script-parse-function)
  (setq proof-script-comment-start "(*")
  (setq proof-script-comment-end "*)")
  (setq proof-unnamed-theorem-name "Unnamed_thm") ; Coq's default name

  (setq proof-assistant-home-page coq-www-home-page)

  (setq proof-prog-name coq-prog-name)
  (setq proof-guess-command-line 'coq-guess-command-line)
  (setq proof-prog-name-guess t)

  ;; We manage file saveing via coq-compile-auto-save and for coq
  ;; it is not necessary to save files when starting a new buffer.
  (setq proof-query-file-save-when-activating-scripting nil)
  
  ;; Commands sent to proof engine
  (setq proof-showproof-command "Show. "
        proof-context-command "Print All. "
        proof-goal-command "Goal %s. "
        proof-save-command "Save %s. "
        proof-find-theorems-command "Search %s. ")
;; FIXME da: Does Coq have a help or about command?
;;	proof-info-command "Help"

  (setq proof-goal-command-p 'coq-goal-command-p
        proof-find-and-forget-fn 'coq-find-and-forget
        pg-topterm-goalhyplit-fn 'coq-goal-hyp
        proof-state-preserving-p 'coq-state-preserving-p)

  (setq proof-query-identifier-command "Check %s.")

  (setq proof-save-command-regexp coq-save-command-regexp
        proof-really-save-command-p 'coq-save-command-p ;pierre:deals with Proof <term>.
	proof-save-with-hole-regexp coq-save-with-hole-regexp
	proof-goal-with-hole-regexp coq-goal-with-hole-regexp
	proof-nested-undo-regexp coq-state-changing-commands-regexp
        proof-script-imenu-generic-expression coq-generic-expression)

  (if (and coq-use-smie (fboundp 'smie-setup))
      (smie-setup coq-smie-grammar #'coq-smie-rules
                  :forward-token #'coq-smie-forward-token
                  :backward-token #'coq-smie-backward-token)
    (require 'coq-indent)
    (setq
     ;; indentation is implemented in coq-indent.el
     indent-line-function 'coq-indent-line
     proof-indent-any-regexp      coq-indent-any-regexp
     proof-indent-open-regexp     coq-indent-open-regexp
     proof-indent-close-regexp    coq-indent-close-regexp)

    (make-local-variable 'indent-region-function)
    (setq indent-region-function 'coq-indent-region))


  ;; span menu
  (setq proof-script-span-context-menu-extensions 'coq-create-span-menu)

  (setq proof-shell-start-silent-cmd "Set Silent. "
        proof-shell-stop-silent-cmd "Unset Silent. ")

  (coq-init-syntax-table)
  ;; we can cope with nested comments
  (set (make-local-variable 'comment-quote-nested) nil)

  ;; font-lock
  (setq proof-script-font-lock-keywords coq-font-lock-keywords-1)

  ;; holes
  (if coq-use-editing-holes (holes-mode 1))

  (proof-config-done)

  ;; outline
  (make-local-variable 'outline-regexp)
  (setq outline-regexp coq-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp coq-outline-heading-end-regexp)

  ;; tags
  (if (file-exists-p coq-tags)
      (set (make-local-variable 'tags-table-list)
           (cons coq-tags tags-table-list)))
  
  (set (make-local-variable
        'blink-matching-paren-dont-ignore-comments) t)

  (setq proof-cannot-reopen-processed-files nil)

  (add-hook 'proof-activate-scripting-hook 'proof-cd-sync nil t))

(defun coq-shell-mode-config ()
  (setq
   proof-shell-cd-cmd coq-shell-cd
   proof-shell-filename-escapes '(("\\\\" . "\\\\") ("\""   . "\\\""))
   proof-shell-clear-goals-regexp coq-shell-proof-completed-regexp
   proof-shell-proof-completed-regexp coq-shell-proof-completed-regexp
   proof-shell-error-regexp coq-error-regexp
   proof-shell-interrupt-regexp coq-interrupt-regexp
   proof-shell-assumption-regexp coq-id
   pg-subterm-first-special-char ?\360
   ;; The next three represent path annotation information
   pg-subterm-start-char ?\372          ; not done
   pg-subterm-sep-char ?\373            ; not done
   pg-subterm-end-char ?\374            ; not done
   pg-topterm-regexp "\375"

   proof-shell-eager-annotation-start "\376\\|\\[Reinterning\\|Warning:"
   proof-shell-eager-annotation-start-length 12

   ;; ****** is added at the end of warnings in emacs mode, this is temporary I
   ;;        want xml like tags, and I want them removed before warning display.
   ;; I want the same for errors -> pgip

   proof-shell-eager-annotation-end "\377\\|done\\]\\|\\*\\*\\*\\*\\*\\*" ; done
   proof-shell-annotated-prompt-regexp coq-shell-prompt-pattern
   proof-shell-result-start "\372 Pbp result \373"
   proof-shell-result-end "\372 End Pbp result \373"

   proof-shell-start-goals-regexp          "^[0-9]+ subgoals?"
   proof-shell-end-goals-regexp nil        ; up to next prompt
   proof-shell-init-cmd coq-shell-init-cmd

   proof-no-fully-processed-buffer t

   ;; Coq has no global settings?
   ;; (proof-assistant-settings-cmd))

   proof-shell-restart-cmd coq-shell-restart-cmd
   pg-subterm-anns-use-stack t)

  (coq-init-syntax-table)
  ;; (holes-mode 1)  da: does the shell really need holes mode on?
  (setq proof-shell-font-lock-keywords 'coq-font-lock-keywords-1)
  (proof-shell-config-done))

(defun coq-goals-mode-config ()
  (setq pg-goals-change-goal "Show %s . ")
  (setq pg-goals-error-regexp coq-error-regexp)
  (coq-init-syntax-table)
  (setq proof-goals-font-lock-keywords coq-font-lock-keywords-1)
  (proof-goals-config-done))

(defun coq-response-config ()
  (coq-init-syntax-table)
  (setq proof-response-font-lock-keywords coq-font-lock-keywords-1)
  ;; The line wrapping in this buffer just seems to make it less readable.
  (setq truncate-lines t)
  (proof-response-config-done))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Flags and other settings for Coq.
;; These appear on the Coq -> Setting menu.
;;

;; FIXME da: we should send this command only inside a proof,
;; otherwise it gives an error message.  It should be on
;; a different menu command.
;; (defpacustom print-only-first-subgoal  nil
;;  "Whether to just print the first subgoal in Coq."
;;  :type 'boolean
;;  :setting ("Focus. " . "Unfocus. "))


;; FIXME: to handle "printing all" properly, we should change the state
;; of the variables that also depend on it.
(defpacustom print-fully-explicit nil
  "Print fully explicit terms."
  :type 'boolean
  :setting ("Set Printing All. " . "Unset Printing All. "))

(defpacustom print-implicit nil
  "Print implicit arguments in applications."
  :type 'boolean
  :setting ("Set Printing Implicit. " . "Unset Printing Implicit. "))

(defpacustom print-coercions nil
  "Print coercions."
  :type 'boolean
  :setting ("Set Printing Coercions. " . "Unset Printing Coercions. "))

(defpacustom print-match-wildcards t
  "Print underscores for unused variables in matches."
  :type 'boolean
  :setting ("Set Printing Wildcard. " . "Unset Printing Wildcard. "))

(defpacustom print-elim-types t
  "Print synthesised result type for eliminations."
  :type 'boolean
  :setting ("Set Printing Synth. " . "Unset Printing Synth. "))

(defpacustom printing-depth 50
  "Depth of pretty printer formatting, beyond which dots are displayed."
  :type 'integer
  :setting "Set Printing Depth %i . ")

(defpacustom undo-depth coq-default-undo-limit
  "Depth of undo history.  Undo behaviour will break beyond this size."
  :type 'integer
  :setting "Set Undo %i . ")

(defpacustom time-commands nil
  "Whether to display timing information for each command."
  :type 'boolean)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Multiple file handling revisited
;;

;; user options and variables

(defgroup coq-auto-compile ()
  "Customization for automatic compilation of required files"
  :group 'coq
  :package-version '(ProofGeneral . "4.1"))

(defpacustom compile-before-require nil
  "If non-nil, check dependencies of required modules and compile if necessary.
If non-nil ProofGeneral intercepts \"Require\" commands and checks if the
required library module and its dependencies are up-to-date. If not, they
are compiled from the sources before the \"Require\" command is processed.

This option can be set/reset via menu
`Coq -> Settings -> Compile Before Require'."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(defcustom coq-compile-command ""
  "External compilation command. If empty ProofGeneral compiles itself.
If unset (the empty string) ProofGeneral computes the dependencies of
required modules with coqdep and compiles as necessary. This internal
dependency checking does currently not handle ML modules.

If a non-empty string, the denoted command is called to do the
dependency checking and compilation. Before executing this
command the following keys are substituted as follows:
  %p  the (physical) directory containing the source of
      the required module
  %o  the Coq object file in the physical directory that will
      be loaded
  %s  the Coq source file in the physical directory whose
      object will be loaded
  %q  the qualified id of the \"Require\" command
  %r  the source file containing the \"Require\"

For instance, \"make -C %p %o\" expands to \"make -C bar foo.vo\"
when module \"foo\" from directory \"bar\" is required.

After the substitution the command can be changed in the
minibuffer if `coq-confirm-external-compilation' is t."
  :type 'string
  :safe '(lambda (v)
           (and (stringp v)
                (or (not (boundp 'coq-confirm-external-compilation))
                    coq-confirm-external-compilation)))
  :group 'coq-auto-compile)

(defpacustom confirm-external-compilation t
  "If set let user change and confirm the compilation command.
Otherwise start the external compilation without confirmation.

This option can be set/reset via menu
`Coq -> Settings -> Confirm External Compilation'."
  :type 'boolean
  :group 'coq-auto-compile)

(defconst coq-compile-substitution-list
  '(("%p" physical-dir)
    ("%o" module-object)
    ("%s" module-source)
    ("%q" qualified-id)
    ("%r" requiring-file))
  "Substitutions for `coq-compile-command'.
Value must be a list of substitutions, where each substitution is
a 2-element list. The first element of a substitution is the
regexp to substitute, the second the replacement. The replacement
is evaluated before passing it to `replace-regexp-in-string', so
it might be a string, or one of the symbols 'physical-dir,
'module-object, 'module-source, 'qualified-id and
'requiring-file, which are bound to, respectively, the physical
directory containing the source file, the Coq object file in
'physical-dir that will be loaded, the Coq source file in
'physical-dir whose object will be loaded, the qualified module
identifier that occurs in the \"Require\" command, and the file
that contains the \"Require\".")

(defcustom coq-compile-auto-save 'ask-coq
  "Buffers to save before checking dependencies for compilation.
There are two orthogonal choices: Firstly one can save all or only the coq
buffers, where coq buffers means all buffers in coq mode except the current
buffer. Secondly, Emacs can ask about each such buffer or save all of them
unconditionally.

This makes four permitted values: 'ask-coq to confirm saving all
modified Coq buffers, 'ask-all to confirm saving all modified
buffers, 'save-coq to save all modified Coq buffers without
confirmation and 'save-all to save all modified buffers without
confirmation."
  :type
  '(radio
    (const :tag "ask for each coq-mode buffer, except the current buffer"
           ask-coq)
    (const :tag "ask for all buffers" ask-all)
    (const
     :tag
     "save all coq-mode buffers except the current buffer without confirmation"
     save-coq)
    (const :tag "save all buffers without confirmation" save-all))
  :safe '(lambda (v) (member v '(ask-coq ask-all save-coq save-all)))
  :group 'coq-auto-compile)

(defcustom coq-lock-ancestors t
  "If non-nil, lock ancestor module files.
If external compilation is used (via `coq-compile-command') then
only the direct ancestors are locked. Otherwise all ancestors are
locked when the \"Require\" command is processed."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(defcustom coq-compile-ignore-library-directory t
  "If non-nil, ProofGeneral does not compile modules from the coq library.
Should be `t' for normal coq users. If `nil' library modules are
compiled if their sources are newer.

This option has currently no effect, because Proof General uses
coqdep to translate qualified identifiers into library file names
and coqdep does not output dependencies in the standard library."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(defcustom coq-compile-ignored-directories nil
  "Directories in which ProofGeneral should not compile modules.
List of regular expressions for directories in which ProofGeneral
should not compile modules. If a library file name matches one
of the regular expressions in this list then ProofGeneral does
neither compile this file nor check its dependencies for
compilation. It makes sense to include non-standard coq library
directories here if they are not changed and if they are so big
that dependency checking takes noticeable time."
  :type '(repeat regexp)
  :safe '(lambda (v) (every 'stringp v))
  :group 'coq-auto-compile)

(defcustom coq-load-path nil
  "Non-standard coq library load path.
List of directories to be added to the LoadPath of coqdep, coqc
and coqtop. Under normal circumstances this list does not need to
contain the coq standard library or \".\" for the current
directory (see `coq-load-path-include-current').

Elements of this list should be strings, which are passed as
\"-I\" options over the command line to coqdep, coqc and coqtop."
  :type '(repeat string)
  :safe '(lambda (v) (every 'stringp v))
  :group 'coq-auto-compile)

(defcustom coq-load-path-include-current t
  "If `t' let coqdep search the current directory too.
Should be `t' for normal users. If `t' pass \"-I dir\" to coqdep when
processing files in directory \"dir\" in addition to any entries
in `coq-load-path'."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(defconst coq-require-command-regexp
  "^Require[ \t\n]+\\(Import\\|Export\\)?[ \t\n]*"
  "Regular expression matching Require commands in Coq.
Should match \"Require\" with its import and export variants up to (but not
including) the first character of the first required module. The required
modules are matched separately with `coq-require-id-regexp'")

(defconst coq-require-id-regexp
  "[ \t\n]*\\([A-Za-z0-9_']+\\(\\.[A-Za-z0-9_']+\\)*\\)[ \t\n]*"
  "Regular expression matching one Coq module identifier.
Should match precisely one complete module identifier and surrounding
white space. The module identifier must be matched with group number 1.
Note that the trailing dot in \"Require A.\" is not part of the module
identifier and should therefore not be matched by this regexp.")

(defvar coq-compile-history nil
  "History of external Coq compilation commands.")

(defvar coq-compile-response-buffer "*coq-compile-response*"
  "Name of the buffer to display error messages from coqc and coqdep.")


(defvar coq-debug-auto-compilation nil
  "*Display more messages during compilation")


;; basic utilities

(defun time-less-or-equal (time-1 time-2)
  "Return `t' if time value time-1 is earlier or equal to time-2.
A time value is a list of two integers as returned by `file-attributes'.
The first integer contains the upper 16 bits and the second the lower
16 bits of the time."
  (or (time-less-p time-1 time-2)
      (equal time-1 time-2)))

(defun coq-max-dep-mod-time (dep-mod-times)
  "Return the maximum in DEP-MOD-TIMES.
Argument DEP-MOD-TIMES is a list where each element is either a
time value (see `time-less-or-equal') or 'just-compiled. The
function returns the maximum of the elements in DEP-MOD-TIMES,
where 'just-compiled is considered the greatest time value. If
DEP-MOD-TIMES is empty it returns nil."
  (let ((max nil))
    (while dep-mod-times
      (cond
       ((eq (car dep-mod-times) 'just-compiled)
        (setq max 'just-compiled
              dep-mod-times nil))
       ((eq max nil)
        (setq max (car dep-mod-times)))
       ((time-less-p max (car dep-mod-times))
        (setq max (car dep-mod-times))))
      (setq dep-mod-times (cdr-safe dep-mod-times)))
    max))


;; Compute command line for starting coqtop

(defun coq-prog-args ()
  ;; coqtop always adds the current directory to the LoadPath, so don't
  ;; include it in the -I options.
  (let ((coq-load-path-include-current nil))
    (append coq-prog-args (coq-include-options nil))))


;; ancestor (un-)locking

(defun coq-lock-ancestor (span ancestor-src)
  "Lock ancestor ANCESTOR-SRC and register it in SPAN.
Lock only if `coq-lock-ancestor' is non-nil. Further, do nothing,
if ANCESTOR-SRC is already a member of
`proof-included-files-list'. Otherwise ANCESTOR-SRC is locked and
registered in the 'coq-locked-ancestors property of the SPAN to
properly unlock ANCESTOR-SRC on retract."
  (if coq-lock-ancestors
      (let ((true-ancestor-src (file-truename ancestor-src)))
        (unless (member true-ancestor-src proof-included-files-list)
          (proof-register-possibly-new-processed-file true-ancestor-src)
          (span-set-property
           span 'coq-locked-ancestors
           (cons true-ancestor-src
                 (span-property span 'coq-locked-ancestors)))))))

(defun coq-unlock-ancestor (ancestor-src)
  "Unlock ANCESTOR-SRC."
  (let* ((true-ancestor (file-truename ancestor-src)))
    (setq proof-included-files-list
          (delete true-ancestor proof-included-files-list))
    (proof-restart-buffers (proof-files-to-buffers (list true-ancestor)))))

(defun coq-unlock-all-ancestors-of-span (span)
  "Unlock all ancestors that have been locked when SPAN was asserted."
  (mapc 'coq-unlock-ancestor (span-property span 'coq-locked-ancestors))
  (span-set-property span 'coq-locked-ancestors ()))

;; handle Require commands when queue is extended

(defun coq-compile-ignore-file (lib-obj-file)
  "Check whether ProofGeneral should handle compilation of LIB-OBJ-FILE.
Return `t' if ProofGeneral should skip LIB-OBJ-FILE and `nil' if
ProofGeneral should handle the file. For normal users it does, for instance,
not make sense to let ProofGeneral check if the coq standard library
is up-to-date."
  (or
   (and
    coq-compile-ignore-library-directory
    (eq (compare-strings coq-library-directory 0 nil
                         lib-obj-file 0 (length coq-library-directory))
        t)
    (if coq-debug-auto-compilation
        (message "Ignore lib file %s" lib-obj-file))
    t)
   (if (some
        (lambda (dir-regexp) (string-match dir-regexp lib-obj-file))
        coq-compile-ignored-directories)
       (progn
         (if coq-debug-auto-compilation
             (message "Ignore %s" lib-obj-file))
         t)
     nil)))

(defun coq-library-src-of-obj-file (lib-obj-file)
  "Return source file name for LIB-OBJ-FILE.
Chops off the last character of LIB-OBJ-FILE to convert \"x.vo\" to \"x.v\"."
  (substring lib-obj-file 0 (- (length lib-obj-file) 1)))

(defun coq-include-options (file)
  "Build a -I options list for coqc and coqdep.
The options list includes all directories from `coq-load-path' and,
if `coq-load-path-include-current' is enabled, the directory base of FILE.
The resulting list is fresh for every call, callers can append more
arguments with `nconc'.

FILE should be an absolute file name. It can be nil if
`coq-load-path-include-current' is nil."
  (let ((result nil))
    (when coq-load-path
      (setq result (list "-I" (expand-file-name (car coq-load-path))))
      (dolist (dir (cdr coq-load-path))
        (nconc result (list "-I" (expand-file-name dir)))))
    (if coq-load-path-include-current
        (setq result
              (cons "-I" (cons (file-name-directory file) result))))
    result))

(defun coq-init-compile-response-buffer (command)
  "Initialize the buffer for the compilation output.
If `coq-compile-response-buffer' exists, empty it. Otherwise
create a buffer with name `coq-compile-response-buffer', put
it into `compilation-mode' and store it in
`coq-compile-response-buffer' for later use. Argument COMMAND is
the command whose output will appear in the buffer."
  (let ((buffer-object (get-buffer coq-compile-response-buffer)))
    (if buffer-object
        (let ((inhibit-read-only t))
          (with-current-buffer buffer-object
            (erase-buffer)))
      (setq buffer-object
            (get-buffer-create coq-compile-response-buffer))
      (with-current-buffer buffer-object
        (compilation-mode)))
    ;; I don't really care if somebody gets the right mode when
    ;; he saves and reloads this buffer. However, error messages in
    ;; the first line are not found for some reason ...
    (let ((inhibit-read-only t))
      (with-current-buffer buffer-object
        (insert "-*- mode: compilation; -*-\n\n" command "\n")))))

(defun coq-display-compile-response-buffer ()
  "Display the errors in `coq-compile-response-buffer'."
  (with-current-buffer coq-compile-response-buffer
    ;; fontification enables the error messages
    (let ((font-lock-verbose nil)) ; shut up font-lock messages
      (font-lock-fontify-buffer)))
  ;; Make it so the next C-x ` will use this buffer.
  (setq next-error-last-buffer (get-buffer coq-compile-response-buffer))
  (let ((window (display-buffer coq-compile-response-buffer)))
    (if proof-shrink-windows-tofit
        (save-excursion
          (save-selected-window
            (proof-resize-window-tofit window))))))

(defun coq-get-library-dependencies (lib-src-file &optional command-intro)
  "Compute dependencies of LIB-SRC-FILE.
Invoke \"coqdep\" on lib-src-file and parse the output to
compute the compiled coq library object files on which
LIB-SRC-FILE depends. The return value is either a string or a
list. If it is a string then an error occurred and the string is
the core of the error message. If the return value is a list no
error occurred and the returned list is the (possibly empty) list
of file names LIB-SRC-FILE depends on.

If an error occurs this funtion displays the
`coq-compile-response-buffer' with the complete command and its
output. The optional argument COMMAND-INTRO is only used in the
error case. It is prepended to the displayed command.

LIB-SRC-FILE should be an absolute file name. If it is, the
dependencies are absolute too and the simplified treatment of
`coq-load-path-include-current' in `coq-include-options' won't
break."
  (let ((coqdep-arguments
         (nconc (coq-include-options lib-src-file) (list lib-src-file)))
        coqdep-output)
    (if coq-debug-auto-compilation
        (message "call coqdep arg list: %s" coqdep-arguments))
    (with-temp-buffer
      (apply 'call-process
       coq-dependency-analyzer nil (current-buffer) nil coqdep-arguments)
      (setq coqdep-output (buffer-string)))
    (if coq-debug-auto-compilation
        (message "coqdep output on %s: %s" lib-src-file coqdep-output))
    (if (string-match "^\\*\\*\\* Warning" coqdep-output)
        (let* ((this-command (cons coq-dependency-analyzer coqdep-arguments))
               (full-command (if command-intro
                                 (cons command-intro this-command)
                               this-command)))
          ;; display the error
          (coq-init-compile-response-buffer
           (mapconcat 'identity full-command " "))
          (let ((inhibit-read-only t))
            (with-current-buffer coq-compile-response-buffer
              (insert coqdep-output)))
          (coq-display-compile-response-buffer)
          "unsatisfied dependencies")
      (if (string-match ": \\(.*\\)$" coqdep-output)
          (cdr-safe (split-string (match-string 1 coqdep-output)))
        ()))))

(defun coq-compile-library (src-file)
  "Recompile coq library SRC-FILE.
Display errors in buffer `coq-compile-response-buffer'."
  (message "Recompile %s" src-file)
  (let ((coqc-arguments
         (nconc (coq-include-options src-file) (list src-file)))
        coqc-status)
    (coq-init-compile-response-buffer
     (mapconcat 'identity (cons coq-compiler coqc-arguments) " "))
    (if coq-debug-auto-compilation
        (message "call coqc arg list: %s" coqc-arguments))
    (setq coqc-status
          (apply 'call-process
           coq-compiler nil coq-compile-response-buffer t coqc-arguments))
    (if coq-debug-auto-compilation
        (message "compilation %s exited with %s, output |%s|"
                 src-file coqc-status
                 (with-current-buffer coq-compile-response-buffer
                   (buffer-string))))
    (unless (eq coqc-status 0)
      (coq-display-compile-response-buffer)
      (let ((terminated-text (if (numberp coqc-status)
                                 "terminated with exit status"
                               "was terminated by signal")))
        (error "ERROR: Recompiling coq library %s %s %s"
               src-file terminated-text coqc-status)))))

(defun coq-compile-library-if-necessary (max-dep-obj-time src obj)
  "Recompile SRC to OBJ if necessary.
This function compiles SRC to the coq library object file OBJ
if one of the following conditions is true:
- a dependency has just been compiled
- OBJ does not exist
- SRC is newer than OBJ
- OBJ is older than the the youngest object file of the dependencies.

Argument MAX-DEP-OBJ-TIME provides the information about the
dependencies. It is either
- 'just-compiled if one of the dependencies of SRC has just
  been compiled
- the time value (see`time-less-or-equal') of the youngest (most
  recently created) object file among the dependencies
- nil if there are no dependencies, or if they are all ignored

If this function decides to compile SRC to OBJ it returns
'just-compiled. Otherwise it returns the modification time of
OBJ.

Note that file modification times inside Emacs have only a
precisision of 1 second. To avoid spurious recompilations we do
not recompile if the youngest object file of the dependencies and
OBJ have identical modification times."
  (let (src-time obj-time)
    (if (eq max-dep-obj-time 'just-compiled)
        (progn
          (coq-compile-library src)
          'just-compiled)
      (setq src-time (nth 5 (file-attributes src)))
      (setq obj-time (nth 5 (file-attributes obj)))
      (if (or
           (not obj-time)                     ; obj does not exist
           (time-less-or-equal obj-time src-time) ; src is newer
           (and
            max-dep-obj-time            ; there is a youngest dependency
                                        ; which is newer than obj
            (time-less-p obj-time max-dep-obj-time)))
          (progn
            (coq-compile-library src)
            'just-compiled)
        (if coq-debug-auto-compilation
            (message "Skip compilation of %s" src))
        obj-time))))

(defun coq-make-lib-up-to-date (coq-obj-hash span lib-obj-file)
  "Make library object file LIB-OBJ-FILE up-to-date.
Check if LIB-OBJ-FILE and all it dependencies are up-to-date
compiled coq library objects. Recompile the necessary objects, if
not. This function returns 'just-compiled if it compiled
LIB-OBJ-FILE. Otherwise it returns the modification time of
LIB-OBJ-FILE as time value (see `time-less-or-equal').

Either LIB-OBJ-FILE or its source file (or both) must exist when
entering this function.

Argument SPAN is the span of the \"Require\" command.
LIB-OBJ-FILE and its dependencies are locked and registered in
the span for for proper unlocking on retract.

Argument COQ-OBJ-HASH remembers the return values of this
function."
  (let ((result (gethash lib-obj-file coq-obj-hash)))
    (if result
        (progn
          (if coq-debug-auto-compilation
              (message "Checked %s already" lib-obj-file))
          result)
      ;; lib-obj-file has not been checked -- do it now
      (message "Check %s" lib-obj-file)
      (if (coq-compile-ignore-file lib-obj-file)
          ;; return minimal time for ignored files
          (setq result '(0 0))
        (let* ((lib-src-file
                (expand-file-name (coq-library-src-of-obj-file lib-obj-file)))
               dependencies deps-mod-time)
          (if (file-exists-p lib-src-file)
              ;; recurse into dependencies now
              (progn
                (setq dependencies (coq-get-library-dependencies lib-src-file))
                (if (stringp dependencies)
                    (error "File %s has %s" lib-src-file dependencies))
                (setq deps-mod-time
                      (mapcar
                       (lambda (dep)
                         (coq-make-lib-up-to-date coq-obj-hash span dep))
                       dependencies))
                (setq result
                      (coq-compile-library-if-necessary
                       (coq-max-dep-mod-time deps-mod-time)
                       lib-src-file lib-obj-file)))
            (message "coq-auto-compile: no source file for %s" lib-obj-file)
            (setq result
                  ;; 5 value: last modification time
                  (nth 5 (file-attributes lib-obj-file))))
          (coq-lock-ancestor span lib-src-file)))
      ;; at this point the result value has been determined
      ;; store it in the hash then
      (puthash lib-obj-file result coq-obj-hash)
      result)))

(defun coq-auto-compile-externally (span qualified-id absolute-module-obj-file)
  "Make MODULE up-to-date according to `coq-compile-command'.
Start a compilation to make ABSOLUTE-MODULE-OBJ-FILE up-to-date.
The compilation command is derived from `coq-compile-command' by
substituting certain keys, see `coq-compile-command' for details.
If `coq-confirm-external-compilation' is t then the user
must confirm the external command in the minibuffer, otherwise
the command is executed without confirmation.

Argument SPAN is the span of the \"Require\" command. The
ancestor ABSOLUTE-MODULE-OBJ-FILE is locked and registered in the
span for for proper unlocking on retract.

This function uses the low-level interface `compilation-start',
therefore the customizations for `compile' do not apply."
  (unless (coq-compile-ignore-file absolute-module-obj-file)
    (let* ((local-compile-command coq-compile-command)
           (physical-dir (file-name-directory absolute-module-obj-file))
           (module-object (file-name-nondirectory absolute-module-obj-file))
           (module-source (coq-library-src-of-obj-file module-object))
           (requiring-file buffer-file-name))
      (mapc
       (lambda (substitution)
         (setq local-compile-command
               (replace-regexp-in-string
                (car substitution) (eval (car (cdr substitution)))
                local-compile-command)))
       coq-compile-substitution-list)
      (if coq-confirm-external-compilation
          (setq local-compile-command
                (read-shell-command
                 "Coq compile command: " local-compile-command
                 (if (equal (car coq-compile-history) local-compile-command)
                     '(coq-compile-history . 1)
                   'coq-compile-history))))
      ;; buffers have already been saved before we entered this function
      ;; the next line is probably necessary to make recompile work
      (setq-default compilation-directory default-directory)
      (compilation-start local-compile-command)
      (coq-lock-ancestor
       span
       (coq-library-src-of-obj-file absolute-module-obj-file)))))

(defun coq-map-module-id-to-obj-file (module-id span)
  "Map MODULE-ID to the appropriate coq object file.
The mapping depends of course on `coq-load-path'. The current
implementation invokes coqdep with a one-line require command.
This is probably slower but much simpler than modelling coq file
loading inside ProofGeneral. Argument SPAN is only used for error
handling. It provides the location information of MODULE-ID for a
decent error message.

A peculiar consequence of the current implementation is that this
function returns () if MODULE-ID comes from the standard library."
  (let ((coq-load-path
         (if coq-load-path-include-current
             (cons default-directory coq-load-path)
           coq-load-path))
        (coq-load-path-include-current nil)
        (temp-require-file (make-temp-file "ProofGeneral-coq" nil ".v"))
        (coq-string (concat "Require " module-id "."))
        result)
    (unwind-protect
        (progn
          (with-temp-file temp-require-file
            (insert coq-string))
          (setq result
                (coq-get-library-dependencies
                 temp-require-file
                 (concat "echo \"" coq-string "\" > " temp-require-file))))
      (delete-file temp-require-file))
    (if (stringp result)
        ;; Error handling: coq-get-library-dependencies was not able to
        ;; translate module-id into a file name. We insert now a faked error
        ;; message into coq-compile-response-buffer to make next-error happy.
        (let ((error-message
               (format "Cannot find library %s in loadpath" module-id))
              (inhibit-read-only t))
          ;; Writing a message into coq-compile-response-buffer for next-error
          ;; does currently not work. We do have exact position information
          ;; about the span, but we don't know how much white space there is
          ;; between the start of the span and the start of the command string.
          ;; Check that coq-compile-response-buffer is a valid buffer!
          ;; (with-current-buffer coq-compile-response-buffer
          ;;   (insert
          ;;    (format "File \"%s\", line %d\n%s.\n"
          ;;            (buffer-file-name (span-buffer span))
          ;;            (with-current-buffer (span-buffer span)
          ;;              (line-number-at-pos (span-start span)))
          ;;            error-message)))
          ;; (coq-display-compile-response-buffer)
          (error error-message)))
    (assert (<= (length result) 1)
            "Internal error in coq-map-module-id-to-obj-file")
    (car-safe result)))

(defun coq-check-module (coq-object-local-hash-symbol span module-id)
  "Locate MODULE-ID and compile if necessary.
If `coq-compile-command' is not nil the whole task of checking which
modules need compilation and the compilation itself is done by an external
process. If `coq-compile-command' is nil ProofGeneral computes the
dependencies with \"coqdep\" and compiles modules as necessary. This internal
checking does currently not handle ML modules.

Argument SPAN is the span of the \"Require\" command. Locked
ancestors are registered in its 'coq-locked-ancestors property
for proper unlocking on retract.

Argument COQ-OBJECT-LOCAL-HASH-SYMBOL provides a place to store
the coq-obj-hash, which is used during internal
compilation (see `coq-make-lib-up-to-date'). This way one hash
will be used for all \"Require\" commands added at once to the
queue."
  (let ((module-obj-file (coq-map-module-id-to-obj-file module-id span)))
    ;; coq-map-module-id-to-obj-file currently returns () for
    ;; standard library modules!
    (when module-obj-file
      (if (> (length coq-compile-command) 0)
          (coq-auto-compile-externally span module-id module-obj-file)
        (unless (symbol-value coq-object-local-hash-symbol)
          (set coq-object-local-hash-symbol (make-hash-table :test 'equal)))
        (coq-make-lib-up-to-date (symbol-value coq-object-local-hash-symbol)
                                 span module-obj-file)))))

(defvar coq-process-require-current-buffer
  "Used in `coq-compile-save-some-buffers' and `coq-compile-save-buffer-filter'.
This only locally used variable communicates the current buffer
from `coq-compile-save-some-buffers' to
`coq-compile-save-buffer-filter'.")

(defun coq-compile-save-buffer-filter ()
  "Filter predicate for `coq-compile-save-some-buffers'.
See also `save-some-buffers'. Returns t for buffers with major mode
'coq-mode' different from coq-process-require-current-buffer and nil
for all other buffers. The buffer to test must be current."
  (and
   (eq major-mode 'coq-mode)
   (not (eq coq-process-require-current-buffer
            (current-buffer)))))
  
(defun coq-compile-save-some-buffers ()
  "Save buffers according to `coq-compile-auto-save'.
Uses the local variable coq-process-require-current-buffer to pass the
current buffer (which contains the Require command) to
`coq-compile-save-buffer-filter'."
  (let ((coq-process-require-current-buffer (current-buffer))
        unconditionally buffer-filter)
    (cond
     ((eq coq-compile-auto-save 'ask-coq)
      (setq unconditionally nil
            buffer-filter 'coq-compile-save-buffer-filter))
     ((eq coq-compile-auto-save 'ask-all)
      (setq unconditionally nil
            buffer-filter nil))
     ((eq coq-compile-auto-save 'save-coq)
      (setq unconditionally t
            buffer-filter 'coq-compile-save-buffer-filter))
     ((eq coq-compile-auto-save 'save-all)
      (setq unconditionally t
            buffer-filter nil)))
    (save-some-buffers unconditionally buffer-filter)))

(defun coq-preprocess-require-commands ()
  "Coq function for `proof-shell-extend-queue-hook'.
If `coq-compile-before-require' is non-nil, this function performs the
compilation (if necessary) of the dependencies."
  (if coq-compile-before-require
      (let (;; coq-object-hash-symbol serves as a pointer to the
            ;; coq-obj-hash (see coq-make-lib-up-to-date). The hash
            ;; will be initialized when needed and stored in the value
            ;; cell of coq-object-hash-symbol. The symbol is initialized
            ;; here to use one hash for all the requires that are added now.
            (coq-object-hash-symbol nil)
            string)
        (dolist (item queueitems)
          (let ((string (mapconcat 'identity (nth 1 item) " ")))
            (when (and string
                       (string-match coq-require-command-regexp string))
              (let ((span (car item))
                    (start (match-end 0)))
                (span-add-delete-action
                 span
                 `(lambda ()
                    (coq-unlock-all-ancestors-of-span ,span)))
                (coq-compile-save-some-buffers)
                ;; now process all required modules
                (while (string-match coq-require-id-regexp string start)
                  (setq start (match-end 0))
                  (coq-check-module 'coq-object-hash-symbol span
                                    (match-string 1 string))))))))))

(add-hook 'proof-shell-extend-queue-hook 'coq-preprocess-require-commands)

;; kill coqtop on script buffer change

(defun coq-switch-buffer-kill-proof-shell ()
  "Kill the proof shell without asking the user.
This function is for `proof-deactivate-scripting-hook'. It kills
the proof shell without asking the user for
confirmation (assuming she agreed already on switching the active
scripting buffer). This is needed to ensure the load path is
correct in the new scripting buffer."
  (unless proof-shell-exit-in-progress
    (proof-shell-exit t)))


(add-hook 'proof-deactivate-scripting-hook
          'coq-switch-buffer-kill-proof-shell
          t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Pre-processing of input string
;;

;; Remark: `action' and `string' are known by `proof-shell-insert-hook'
(defun coq-preprocessing ()
  (if coq-time-commands
      (with-no-warnings  ;; NB: dynamic scoping of `string'
        (setq string (concat "Time " string)))))

(add-hook 'proof-shell-insert-hook 'coq-preprocessing)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Subterm markup -- it was added to Coq by Healf, but got removed.
;;                   Let's try faking something by regexp matching.

;; FIXME: not operational yet
(defun coq-fake-constant-markup ()
  "Markup constants in Coq goal output by matching on regexps.
This is a horrible and approximate way of doing subterm markup.
\(Code used to be in Coq, but got lost between versions 5 and 7).
This is a hook setting for `pg-after-fontify-output-hook' to
enable identifiers to be highlighted and allow useful
mouse activation."
  (goto-char (point-min))
  (while (re-search-forward "\(\w+[^\w]\)" nil t)
    (replace-match "\372\200\373\\1\374" nil t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Context-senstive in-span menu additions
;;

(defun coq-create-span-menu (span idiom name)
  (if (eq idiom 'proof)
      (let ((thm (span-property span 'name)))
        (list (vector
               "Check" ; useful?
               `(proof-shell-invisible-command
                 ,(format "Check %s." thm)))
              (vector
               "Print"
               `(proof-shell-invisible-command
                 ,(format "Print %s." thm)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Some smart insertion functions
;;

(defconst module-kinds-table
  '(("Section" 0) ("Module" 1) ("Module Type" 2) ("Declare Module" 3))
  "Enumerates the different kinds of modules.")

(defconst modtype-kinds-table
  '(("" 1) (":" 2) ("<:" 3))
  "Enumerates the different kinds of type information for modules.")

(defun coq-insert-section-or-module ()
  "Insert a module or a section after asking right questions."
  (interactive)
  (let*
      ((mods (completing-read "Kind of module (TAB to see list): " module-kinds-table))
       (s (read-string  "Name: "))
       (typkind (if (string-equal mods "Section")
                    "" ;; if not a section
                  (completing-read "Kind of type (optional, TAB to see list): "
                                   modtype-kinds-table)))
       (p (point)))
    (if (string-equal typkind "")
        (progn
          (insert mods " " s ".\n#\nEnd " s ".")
          (holes-replace-string-by-holes-backward p)
          (goto-char p))
      (insert mods " " s " " typkind " #.\n#\nEnd " s ".")
      (holes-replace-string-by-holes-backward p)
      (goto-char p)
      (holes-set-point-next-hole-destroy))))

(defconst reqkinds-kinds-table
  '(("Require" 1) ("Require Export" 2) ("Import" 3))
  "Enumerates the different kinds of requiring a module.")

(defun coq-insert-requires ()
  "Insert requires to modules, iteratively."
  (interactive)
  (let* ((s)
         (reqkind
          (completing-read
           "Command (TAB to see list, default Require Export) : "
           reqkinds-kinds-table nil nil nil nil "Require Export")))
    (setq s (read-string  "Name (empty to stop) : "))
    (while (not (string-equal s ""))
      (insert (format "%s %s.\n" reqkind s))
      (setq s (read-string  "Name (empty to stop) : ")))))

(defun coq-end-Section ()
  "Ends a Coq section."
  (interactive)
  (let ((count 1)) ; The number of section already "Ended" + 1
    (let ((section
	   (save-excursion
	     (progn
	       (while (and (> count 0)
			   (search-backward-regexp
			    "Chapter\\|Section\\|End" 0 t))
		 (if (char-equal (char-after (point)) ?E)
		     (setq count (1+ count))
		   (setq count (1- count))))
	       (buffer-substring-no-properties
          (progn (beginning-of-line) (forward-word 1) (point))
          (progn (end-of-line) (point)))))))
      (insert (concat "End" section)))))

(defun coq-insert-intros ()
  "Insert an intros command with names given by Show Intros.
Based on idea mentioned in Coq reference manual."
  (interactive)
  (let* ((shints (proof-shell-invisible-cmd-get-result "Show Intros."))
         (intros (replace-regexp-in-string "^\\([^\n]+\\)\n"  "intros \\1." shints t)))
    (if (or (< (length shints) 2);; empty response is just NL
            (string-match coq-error-regexp shints))
        (error "Don't know what to intro")
      (insert intros)
      (indent-according-to-mode))))

(defun coq-insert-infoH-hook ()
  (with-no-warnings  ;; NB: dynamic scoping of `string'
    (setq string (concat "infoH " string))))

;; da: FIXME untested with new generic hybrid code: hope this still works
(defun coq-insert-as ()
  "Insert \"as\" suffix to next command, names given by \"infoH\" tactical.
Based on idea mentioned in Coq reference manual."
  (interactive)
  (add-hook 'proof-shell-insert-hook 'coq-insert-infoH-hook)
  (proof-assert-next-command-interactive)
  (remove-hook 'proof-shell-insert-hook 'coq-insert-infoH-hook);as soone as possible
  (proof-shell-wait)
  (let
      ((str (string-match "<info type=\"infoH\">\\([^<]*\\)</info>"
                          proof-shell-last-response-output))
       (substr (match-string 1 proof-shell-last-response-output)))
    (coq-script-parse-cmdend-backward)
    (let ((inhibit-read-only t))
      (insert (concat " as " substr)))))


(defun coq-insert-match ()
  "Insert a match expression from a type name by Show Match.
Based on idea mentioned in Coq reference manual.
Also insert holes at insertion positions."
  (interactive)
  (proof-shell-ready-prover)
  (let* ((cmd))
    (setq cmd (read-string "Build match for type: "))
    (let* ((thematch
           (proof-shell-invisible-cmd-get-result (concat "Show Match " cmd ".")))
           (match (replace-regexp-in-string "=> \n" "=> #\n" thematch)))
      ;; if error, it will be displayed in response buffer (see def of
      ;; proof-shell-invisible-cmd-get-result), otherwise:
      (unless (proof-string-match coq-error-regexp match)
        (let ((start (point)))
          (insert match)
          (indent-region start (point) nil)
          (let ((n (holes-replace-string-by-holes-backward start)))
            (case n
	(0 nil)				; no hole, stay here.
	(1
	 (goto-char start)
	 (holes-set-point-next-hole-destroy)) ; if only one hole, go to it.
	(t
	 (goto-char start)
	 (message
          (substitute-command-keys
           "\\[holes-set-point-next-hole-destroy] to jump to active hole.  \\[holes-short-doc] to see holes doc."))))))))))

(defun coq-insert-solve-tactic ()
  "Ask for a closing tactic name, with completion, and insert at point.
Completion is on a quasi-exhaustive list of Coq closing tactics."
  (interactive)
  (coq-insert-from-db coq-solve-tactics-db "Closing tactic"))

(defun coq-insert-tactic ()
  "Insert a tactic name at point, with completion.
Questions may be asked to the user to select the tactic."
  (interactive)
  (coq-insert-from-db coq-tactics-db "Tactic"))

(defun coq-insert-tactical ()
  "Ask for a closing tactic name, with completion, and insert at point.
Completion is on a quasi-exhaustive list of Coq tacticals."
  (interactive)
  (coq-insert-from-db coq-tacticals-db "Tactical"))

(defun coq-insert-command ()
  "Ask for a command name, with completion, and insert it at point."
  (interactive)
  (coq-insert-from-db coq-commands-db "Command"))

(defun coq-insert-term ()
  "Ask for a term kind, with completion, and insert it at point."
  (interactive)
  (coq-insert-from-db coq-terms-db "Kind of term"))

(define-key coq-keymap [(control ?i)] 'coq-insert-intros)
(define-key coq-keymap [(control ?m)] 'coq-insert-match)
(define-key coq-keymap [(control ?()] 'coq-insert-section-or-module)
(define-key coq-keymap [(control ?))] 'coq-end-Section)
(define-key coq-keymap [(control ?s)] 'coq-Show)
(define-key coq-keymap [(control ?t)] 'coq-insert-tactic)
(define-key coq-keymap [?t] 'coq-insert-tactical)
(define-key coq-keymap [?r] 'proof-store-response-win)
(define-key coq-keymap [?g] 'proof-store-goals-win)

(define-key coq-keymap [?!] 'coq-insert-solve-tactic) ; will work in tty

(define-key coq-keymap [(control ?\s)] 'coq-insert-term)
(define-key coq-keymap [(control return)] 'coq-insert-command)


(define-key coq-keymap [(control ?r)] 'coq-insert-requires)
(define-key coq-keymap [(control ?o)] 'coq-SearchIsos)

(define-key coq-keymap [(control ?p)] 'coq-Print)
(define-key coq-keymap [(control ?b)] 'coq-About)
(define-key coq-keymap [(control ?a)] 'coq-SearchAbout)
(define-key coq-keymap [(control ?c)] 'coq-Check)
(define-key coq-keymap [?h] 'coq-PrintHint)
(define-key coq-keymap [(control ?l)] 'coq-LocateConstant)
(define-key coq-keymap [(control ?n)] 'coq-LocateNotation)


(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?c)] 'coq-Check)
(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?p)] 'coq-Print)
(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?o)] 'coq-SearchIsos)
(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?b)] 'coq-About)
(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?a)] 'coq-SearchAbout)
;; Window auto-resize makes this bug sometimes. Too bad!.
;; (define-key coq-response-mode-map [(control ?c)(control ?a)(control ?c)] 'coq-Check)

;;;;;;;;;;;;;;;;;;;;;;;;
;; error handling
;;;;;;;;;;;;;;;;;;;;;;;;


(defvar last-coq-error-location nil
  "Last error from `coq-get-last-error-location' and `coq-highlight-error'.")


;; I don't use proof-shell-last-ouput here since it is not always set to the
;; really last output (specially when a *tactic* gives an error) instead I go
;; directly to the response buffer. This allows also to clean the response
;; buffer (better to only scroll it?)
(defun coq-get-last-error-location (&optional parseresp clean)
  "Return location information on last error sent by coq.
Return a two elements list (POS LEN) if successful, nil otherwise.
POS is the number of characters preceding the underlined expression,
and LEN is its length.
Coq error message must be like this:

\"
> command with an error here ...
>                       ^^^^
\"

If PARSERESP is nil, don't really parse response buffer but take the value of
`last-coq-error-location' instead, otherwise parse response buffer and updates
`last-coq-error-location'.

If PARSERESP and CLEAN are non-nil, delete the error location from the response
buffer."
  (if (not parseresp) last-coq-error-location
    ;; proof-shell-handle-error-or-interrupt-hook is called from shell buffer
    (proof-with-current-buffer-if-exists proof-response-buffer
      (goto-char (point-max))
      (when (re-search-backward "\n> \\(.*\\)\n> \\([^^]*\\)\\(\\^+\\)\n" nil t)
        (let ((text (match-string 1))
              (pos (length (match-string 2)))
              (len (length (match-string 3))))
          ;; clean the response buffer from ultra-ugly underlined command line
          ;; parsed above. Don't kill the first \n
          (let ((inhibit-read-only t))
            (when clean (delete-region (+ (match-beginning 0) 1) (match-end 0))))
          (when proof-shell-unicode ;; TODO: remove this (when...) when coq-8.3 is out.
            ;; `pos' and `len' are actually specified in bytes, apparently. So
            ;; let's convert them, assuming the encoding used is utf-8.
            ;; Presumably in Emacs-23 we could use `string-bytes' for that
            ;; since the internal encoding happens to use utf-8 as well.
            ;; Actually in coq-8.3 one utf8 char = one space so we do not need
            ;; this at all
            (let ((bytes text)) ;(encode-coding-string text 'utf-8-unix)
              ;; Check that pos&len make sense in `bytes', if not give up.
              (when (>= (length bytes) (+ pos len))
                ;; We assume here that `text' is a single line and use \n as
                ;; a marker so we can find it back after decoding.
                (setq bytes (concat (substring bytes 0 pos)
                                    "\n" (substring bytes pos (+ pos len))))
                (let ((chars (decode-coding-string bytes 'utf-8-unix)))
                  (setq pos (string-match "\n" chars))
                  (setq len (- (length chars) pos 1))))))
          (setq last-coq-error-location (list pos len)))))))


(defun coq-highlight-error (&optional parseresp clean)
  "Parses the last coq output looking at an error message. Highlight the text
pointed by it. Coq error message must be like this:

\"
> command with an error here ...
>                       ^^^^
\"

If PARSERESP is nil, don't really parse response buffer but take the value of
`last-coq-error-location' instead, otherwise parse response buffer and updates
`last-coq-error-location'.

If PARSERESP and CLEAN are non-nil, delete the error location from the response
buffer."
  (proof-with-current-buffer-if-exists proof-script-buffer
    (let ((mtch (coq-get-last-error-location parseresp clean)))
      (when mtch
        (let ((pos (car mtch))
              (lgth (cadr mtch)))
          (goto-char (+ (proof-unprocessed-begin) 1))
          (coq-find-real-start)
          
          ;; utf8 adaptation is made in coq-get-last-error-location above
          (goto-char (+ (point) pos))
          (span-make-self-removing-span (point) (+ (point) lgth)
                                        'face 'proof-warning-face))))))

(defun coq-highlight-error-hook ()
  (coq-highlight-error t t))

(add-hook 'proof-shell-handle-error-or-interrupt-hook 'coq-highlight-error-hook t)


;;
;; Scroll response buffer to maximize display of first goal
;;

(defun first-word-of-buffer ()
  "Get the first word of a buffer."
  (save-excursion
    (goto-char (point-min))
    (buffer-substring (point)
                      (progn (forward-word 1) (point)))))


(defun coq-show-first-goal ()
  "Scroll the goal buffer so that the first goal is visible.
First goal is displayed on the bottom of its window, maximizing the
number of hypothesis displayed, without hiding the goal"
  (interactive)
  (let ((goal-win (get-buffer-window proof-goals-buffer)))
    (if goal-win
        (with-selected-window goal-win
          ;; find snd goal or buffer end
          (search-forward-regexp "subgoal 2\\|\\'")
          (beginning-of-line)
          ;; find something else than a space
          (ignore-errors (search-backward-regexp "\\S-"))
          (recenter (- 1)) ; put it at bottom og window
          (beginning-of-line)))))

(defvar coq-modeline-string2 ")")
(defvar coq-modeline-string1 ")")
(defvar coq-modeline-string0 " Script(")
(defun coq-build-subgoals-string (n)
  (concat coq-modeline-string0 (int-to-string n)
          (if (> n 1) coq-modeline-string2
            coq-modeline-string1)))

(defun coq-update-minor-mode-alist ()
  "Modify `minor-mode-alist' to display the number of subgoals in the modeline."
  (save-window-excursion ; switch to buffer even if not visible
    (switch-to-buffer proof-goals-buffer)
    (let* ((nbgoals (string-to-number (first-word-of-buffer)))
           (dummy (switch-to-buffer proof-script-buffer))
           (toclean (assq 'proof-active-buffer-fake-minor-mode minor-mode-alist)))
      (while toclean ;; clean minor-mode-alist
        (setq minor-mode-alist (remove toclean minor-mode-alist))
        (setq toclean (assq 'proof-active-buffer-fake-minor-mode minor-mode-alist)))
      (setq minor-mode-alist
            (append (list (list 'proof-active-buffer-fake-minor-mode
                                (coq-build-subgoals-string nbgoals)))
                    minor-mode-alist
                    )))))




;; This hook must be added before optim-resp-window, in order to be evaluated
;; *after* windows resizing.
(add-hook 'proof-shell-handle-delayed-output-hook
	  'coq-show-first-goal)
(add-hook 'proof-shell-handle-delayed-output-hook
	  'coq-update-minor-mode-alist)
(add-hook 'proof-shell-handle-delayed-output-hook
          '(lambda ()
             (if (proof-string-match coq-shell-proof-completed-regexp
                                     proof-shell-last-output)
                 (proof-clean-buffer proof-goals-buffer))))


(defun is-not-split-vertic (selected-window)
  (<= (- (frame-height) (window-height)) 2))


;; *Experimental* auto shrink response buffer in three windows mode. Things get
;; a bit messed up if the response buffer is not at the right place (below
;; goals buffer) TODO: Have this linked to proof-resize-window-tofit in
;; proof-utils.el + customized by the "shrink to fit" menu entry
;;  + have it on by default when in three windows mode.
(defun optim-resp-windows ()
  "Resize response buffer to optimal size.
Only when three-buffer-mode is enabled."
  (when (and proof-three-window-enable
             (> (frame-height) 10)
             (get-buffer-window proof-response-buffer))
    (let ((curwin (selected-window))
          ;; maxhgth is the max height of both resp and goals buffers to avoid
          ;; make the other disappear
          (maxhgth (- (window-height) window-min-height))
          hgt-resp nline-resp)
      (select-window (get-buffer-window proof-response-buffer))
      (setq hgt-resp (window-height))
      (setq nline-resp ; number of lines we want for response buffer
            (min maxhgth (max window-min-height ; + 1 here for comfort
                              (+ 1 (count-lines (point-max) (point-min))))))
      (unless (is-not-split-vertic (selected-window))
        (shrink-window (- hgt-resp nline-resp)))
      (goto-char (point-min))
      (recenter)
      (select-window curwin)
      )))

;; TODO: I would rather have a response-insert-hook thant this two hooks
;; Careful: optim-resp-windows must be called AFTER proof-show-first-goal
;; Adapt when displaying a normal message
(add-hook 'proof-shell-handle-delayed-output-hook 'optim-resp-windows)
;; Adapt when displaying an error or interrupt
(add-hook 'proof-shell-handle-error-or-interrupt-hook 'optim-resp-windows)

(provide 'coq)



;;   Local Variables: ***
;;   fill-column: 79 ***
;;   indent-tabs-mode: nil ***
;;   coding: utf-8 ***
;;   End: ***

;;; coq.el ends here
