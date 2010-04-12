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
  (require 'span)
  (require 'outline)
  (require 'newcomment)
  (defvar coq-time-commands nil)        ; defpacustom
  (defvar coq-auto-compile-vos nil)     ; defpacustom
  (proof-ready-for-assistant 'coq))     ; compile for coq

(require 'proof)
(require 'coq-local-vars)               ;
(require 'coq-syntax)                   ; sets coq-prog-name
(require 'coq-abbrev)                   ; coq specific menu



;; ----- coq-shell configuration options

;;; Code:
;; debugging functions
;; (defun proofstack () (coq-get-span-proofstack (span-at (point) 'type)))
;; End debugging

;; coq-prog-args is the user-set list of arguments to pass to Coq process,
;; see 'defpacustom prog-args' in proof-config for documentation.

;; For Coq, this should contain -emacs.
;; -translate will be added automatically to this list if `coq-translate-to-v8'
;; is set.  The list is not altered if the user has set this herself.

(defcustom coq-translate-to-v8 nil
  "*Whether to use -translate argument to Coq"
  :type 'boolean
  :group 'coq)

;; Fixes default prog args, this is overridden by file variables
(defun coq-build-prog-args ()
  (setq coq-prog-args
        (append (remove-if (lambda (x) (string-match "\\-emacs" x)) coq-prog-args)
                '("-emacs-U")
                (if coq-translate-to-v8 " -translate"))))

;; fix it
(unless noninteractive ;; compiling
  (coq-build-prog-args))

(defcustom coq-compile-file-command "coqc %s"
  "*Command to compile a coq file.
This is called when `coq-auto-compile-vos' is set, unless a Makefile
exists in the directory, in which case the `compile' command is run.
To disable coqc being called (and use only make), set this to nil."
  :type 'string
  :group 'coq)

(defcustom coq-use-makefile nil
  "*Whether to look for a Makefile to attempt to guess the command line.
Set to t if you want this feature."
  :type 'string
  :group 'coq)

;; Command to initialize the Coq Proof Assistant

(defcustom coq-default-undo-limit 300
  "Maximum number of Undo's possible when doing a proof."
  :type 'number
  :group 'coq)

(defconst coq-shell-init-cmd
  (format "Set Undo %s . " coq-default-undo-limit))

(require 'coq-syntax)
(require 'coq-indent)

(defcustom coq-prog-env nil
  "*List of environment settings d to pass to Coq process.
On Windows you might need something like:
  (setq coq-prog-env '(\"HOME=C:\\Program Files\\Coq\\\"))"
  :group 'coq)


;; Command to reset the Coq Proof Assistant
(defconst coq-shell-restart-cmd "Reset Initial.\n ")

(defvar coq-shell-prompt-pattern
  "\\(?:\n\\(?:[^\n\371]+\371\\|<prompt>[^\n]+</prompt>\\)\\)"
  "*The prompt pattern for the inferior shell running coq.")

;; FIXME da: this was disabled (set to nil) -- why?
;; da: 3.5: add experimetntal
;; am:answer: because of bad interaction
;; with coq -R option.
(defvar coq-shell-cd nil
;;  "Add LoadPath \"%s\"." ;; fixes unadorned Require (if .vo exists).
  "*Command of the inferior process to change the directory.")

(defvar coq-shell-proof-completed-regexp "Subtree\\s-proved!\\|Proof\\s-completed"
  "*Regular expression indicating that the proof has been completed.")

(defvar coq-goal-regexp
  "\\(============================\\)\\|\\(subgoal [0-9]+ is:\\)\n")



;; Configuration

(defun coq-library-directory ()
  (let ((c (substring (shell-command-to-string "coqtop -where") 0 -1 )))
    (if (string-match c "not found")
	  "/usr/local/lib/coq"
      c)))


(defcustom coq-tags (concat (coq-library-directory) "/theories/TAGS")
  "The default TAGS table for the Coq library."
  :type 'string
  :group 'coq)

(defconst coq-interrupt-regexp "User Interrupt."
  "Regexp corresponding to an interrupt.")

;; ----- web documentation

(defcustom coq-www-home-page "http://coq.inria.fr/"
  "Coq home page URL."
  :type 'string
  :group 'coq)

;; ----- outline
;; FIXME, deal with interacive "Definition"
(defvar coq-outline-regexp
;;  (concat "(\\*\\|"
  (concat "[ ]*" (regexp-opt
	   '(
             "Ltac" "Corr" "Modu" "Sect" "Chap" "Goal" "Definition" "Lemm" "Theo" "Fact" "Rema" "Mutu" "Fixp" "Func") t)))
;)

(defvar coq-outline-heading-end-regexp "\\.[ \t\n]")

(defvar coq-shell-outline-regexp coq-goal-regexp)
(defvar coq-shell-outline-heading-end-regexp coq-goal-regexp)



;; some of them must kept when v8.1 because they are used by state preserving
;; check when C-c C-v
(defconst coq-state-preserving-tactics-regexp
  (proof-ids-to-regexp coq-state-preserving-tactics))
(defconst coq-state-changing-commands-regexp
  (proof-ids-to-regexp coq-keywords-state-changing-commands))
(defconst coq-state-preserving-commands-regexp
  (proof-ids-to-regexp coq-keywords-state-preserving-commands))
(defconst coq-commands-regexp
  (proof-ids-to-regexp coq-keywords-commands))
(defvar coq-retractable-instruct-regexp
  (proof-ids-to-regexp coq-retractable-instruct))
(defvar coq-non-retractable-instruct-regexp
  (proof-ids-to-regexp coq-non-retractable-instruct))

;;
;;   Derived modes - define keymaps
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's coq specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-set-undo-limit (undos)
  (proof-shell-invisible-command (format "Set Undo %s . " undos)))

;; make this non recursive?
(defun build-list-id-from-string (s)
  "Build a list of string from a string S of the form \"id1|id2|...|idn\"."
  (if (or (not s) (string= s "")) '()
    (let ((x (string-match (concat "\\(" coq-id-shy "\\)\\(?:|\\|\\'\\)\\(.*\\)") s)))
      (if (not x) (error "cannot extract list of ids from string")
        (cons (match-string 1 s)
              (build-list-id-from-string (match-string 2 s))
              )))
    )
  )

;; Use the statenumber inside the coq prompt to backtrack more easily
(defun coq-last-prompt-info (s)
  "Extract info from the coq prompt S.  See `coq-last-prompt-info-safe'."
  (let ((lastprompt (or s (error "no prompt !!?")))
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
used see coq-set-state-number. Initially 1 because Coq initial state has number 1.")

(defvar coq-last-but-one-proofnum 1
  "As for `coq-last-but-one-statenum' but for stack depth.")

(defvar coq-last-but-one-proofstack '()
  "As for `coq-last-but-one-statenum' but for proof stack symbols.")

(defun coq-get-span-statenum (span)
  "Return the state number of the SPAN."
  (span-property span 'statenum)
  )

(defun coq-get-span-proofnum (span)
  "Return the proof number of the SPAN."
  (span-property span 'proofnum)
  )

(defun coq-get-span-proofstack (span)
  "Return the proof stack (names of pending proofs) of the SPAN."
  (span-property span 'proofstack)
  )

(defun coq-set-span-statenum (span val)
  "Set the state number of the SPAN to VAL."
  (span-set-property span 'statenum val)
  )

(defun coq-get-span-goalcmd (span)
  "Return the 'goalcmd flag of the SPAN."
  (span-property span 'goalcmd)
  )

(defun coq-set-span-goalcmd (span val)
  "Set the 'goalcmd flag of the SPAN to VAL."
  (span-set-property span 'goalcmd val)
  )

(defun coq-set-span-proofnum (span val)
  "Set the proof number of the SPAN to VAL."
  (span-set-property span 'proofnum val)
  )

(defun coq-set-span-proofstack (span val)
  "Set the proof stack (names of pending proofs) of the SPAN to VAL."
  (span-set-property span 'proofstack val)
  )

(defun proof-last-locked-span ()
  (save-excursion ;; didn't found a way to avoid buffer switching
    (set-buffer proof-script-buffer)
    (span-at (- (proof-unprocessed-begin) 1) 'type)
    )
  )

;; Each time the state changes (hook below), (try to) put the state number in the
;; last locked span (will fail if there is already a number which should happen when
;; going back in the script).  The state number we put is not the last one because
;; the last one has been sent by Coq *after* the change. We use
;; `coq-last-but-one-statenum' instead and then update it.

;;TODO update docstring and comment

(defun coq-set-state-infos ()
  "Set the last locked span's state number to the number found last time.
This number is in the *last but one* prompt (variable `coq-last-but-one-statenum').
If locked span already has a state number, then do nothing. Also updates
`coq-last-but-one-statenum' to the last state number for next time."
  (if (and proof-shell-last-prompt proof-script-buffer)
      ;; infos = promt infos of the very last prompt
      ;; sp = last locked span, which we want to fill with prompt infos
      (let ((sp    (proof-last-locked-span))
            (infos (or (coq-last-prompt-info-safe) '(0 0 nil)))
            )
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
        (setq coq-last-but-one-proofnum (car (cdr infos)))
        )
    )
  )

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
;; aux < 12 |aux|SmallStepAntiReflexive| 4 < ù
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
  (let* (ans (naborts 0) (nundos 0)
             (proofdepth (coq-get-span-proofnum span))
             (proofstack (coq-get-span-proofstack span))
             (span-staten (coq-get-span-statenum span))
             (naborts (count-not-intersection 
                       coq-last-but-one-proofstack proofstack)))
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
               naborts)))))

(defvar coq-current-goal 1
  "Last goal that Emacs looked at.")

(defun coq-goal-hyp ()
  (cond
   ((looking-at "============================\n")
    (goto-char (match-end 0))
    (cons 'goal (int-to-string coq-current-goal)))
   ((looking-at "subgoal \\([0-9]+\\) is:\n")
    (goto-char (match-end 0))
    (cons 'goal (match-string 1))
    (setq coq-current-goal (string-to-number (match-string 1))))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))

(defun coq-state-preserving-p (cmd)
;  (or
   (proof-string-match coq-non-retractable-instruct-regexp cmd))
;   (and
;    (not (proof-string-match coq-retractable-instruct-regexp cmd))
;    (or
;     (message "Unknown command, hopes this won't desynchronize ProofGeneral")
;     t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to coq                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defconst notation-print-kinds-table
  '(("Print Scope(s)" 0) ("Print Visibility" 1))
  "Enumerates the different kinds of notation information one can ask to coq.")

(defun coq-PrintScope ()
  "Show information on notations. Coq specific."
  (interactive)
  (let*
      ((mods
        (completing-read "Infos on notation (tab to see list): "
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
          ((not (eq mark-active nil)) ; region exists
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

(defun coq-SearchIsos ()
  "Search a term whose type is isomorphic to given type.
This is specific to `coq-mode'."
  (interactive)
  (coq-ask-do "SearchPattern (parenthesis mandatory), ex: (?X1 + _ = _ + ?X1)" "SearchPattern" nil))

(defun coq-SearchConstant ()
  (interactive)
  (coq-ask-do "Search constant" "Search" nil))

(defun coq-SearchRewrite ()
  (interactive)
  (coq-ask-do "Search Rewrite" "SearchRewrite" nil))

(defun coq-SearchAbout ()
  (interactive)
  (coq-ask-do "Search About" "SearchAbout" nil))

(defun coq-Print () "Ask for an ident and print the corresponding term."
  (interactive)
  (coq-ask-do "Print" "Print"))

(defun coq-About () "Ask for an ident and print information on it."
  (interactive)
  (coq-ask-do "About" "About"))

(defun coq-LocateConstant ()
  "Locate a constant.
This is specific to `coq-mode'."
  (interactive)
  (coq-ask-do "Locate" "Locate"))

(defun coq-LocateLibrary ()
  "Locate a constant.
This is specific to `coq-mode'."
  (interactive)
  (coq-ask-do "Locate Library" "Locate Library"))

(defun coq-addquotes (s) (concat "\"" s "\""))

(defun coq-LocateNotation ()
  "Locate a notation.
This is specific to `coq-mode'."
  (interactive)
  (coq-ask-do "Locate Notation (ex: \'exists\' _ , _)" "Locate"
              t 'coq-addquotes))

(defun coq-Pwd ()
  "Locate a notation.
This is specific to `coq-mode'."
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
;            ((file-exists-p (concat dir "../Makefile")) "..")
;            ((file-exists-p (concat dir "../../Makefile")) "../..")
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

;; TODO: complete and maybe make this generic (with prover-specific default?
;; or use same mechanism as tokens, etc?)
(defpacustom use-editing-holes nil
  "Enable holes for editing."
  :type 'boolean)
;;  :eval (set-stuff-for-holes)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-mode-config ()
  ;; Tags is unusable with Coq library otherwise:
  ; da: doesn't exist in GNU Emacs tags
  ;(set (make-local-variable 'tags-always-exact) t)
  ;; Coq error messages are thrown off by TAB chars.
  (set (make-local-variable 'indent-tabs-mode) nil)
  (setq proof-terminal-char ?\.)
  (setq proof-script-command-end-regexp
        "\\(?:[^.]\\|\\(?:\\.\\.\\)\\)\\.\\(\\s-\\|\\'\\)")
  (setq proof-script-comment-start "(*")
  (setq proof-script-comment-end "*)")
  (setq proof-unnamed-theorem-name "Unnamed_thm") ; Coq's default name

  (setq proof-assistant-home-page coq-www-home-page)

  (setq proof-prog-name coq-prog-name)
  (setq proof-guess-command-line 'coq-guess-command-line)
  (setq proof-prog-name-guess t)

  ;; Commands sent to proof engine
  (setq proof-showproof-command "Show. "
        proof-context-command "Print All. "
        proof-goal-command "Goal %s . "
        proof-save-command "Save %s . "
        proof-find-theorems-command "Search %s . ")
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
  proof-script-imenu-generic-expression coq-generic-expression
  )

  (setq
   indent-line-function 'coq-indent-line
;indentation is implemented in coq-indent.el
;   proof-indent-enclose-offset  (- proof-indent)
;   proof-indent-enclose-offset 0
;   proof-indent-close-offset 0
;   proof-indent-open-offset 0
   proof-indent-any-regexp      coq-indent-any-regexp
;   proof-indent-inner-regexp    coq-indent-inner-regexp
;   proof-indent-enclose-regexp  coq-indent-enclose-regexp
   proof-indent-open-regexp     coq-indent-open-regexp
   proof-indent-close-regexp    coq-indent-close-regexp
   )

  (make-local-variable 'indent-region-function)
  (setq indent-region-function 'coq-indent-region)


  ;; span menu
  (setq proof-script-span-context-menu-extensions 'coq-create-span-menu)

  (setq proof-shell-start-silent-cmd "Set Silent. "
        proof-shell-stop-silent-cmd "Unset Silent. ")

  (coq-init-syntax-table)
  (set (make-local-variable 'comment-quote-nested) nil) ;; we can cope with nested comments

  ;; font-lock
  (setq proof-script-font-lock-keywords coq-font-lock-keywords-1)
  ;;holes
  (holes-mode 1)

  (proof-config-done)

  ;; outline
  (make-local-variable 'outline-regexp)
  (setq outline-regexp coq-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp coq-outline-heading-end-regexp)

  ;; tags  ; NOTE da: is this XEmacs tags only?
  (and (boundp 'tag-table-alist)
       (setq tag-table-alist
             (append '(("\\.v$" . coq-tags)
                       ("coq"  . coq-tags))
                     tag-table-alist)))

  (set (make-local-variable 'blink-matching-paren-dont-ignore-comments) t)

  ;; multiple file handling
  (setq proof-cannot-reopen-processed-files t
        ;; proof-shell-inform-file-retracted-cmd 'coq-retract-file
        proof-shell-require-command-regexp coq-require-command-regexp
        proof-done-advancing-require-function 'coq-process-require-command)

  ;; FIXME: PG 3.5, next one shouldn't be needed but setting is
  ;; now lost in define-derived-mode for some reason.
  (add-hook 'proof-activate-scripting-hook 'proof-cd-sync nil t)
  (add-hook 'proof-deactivate-scripting-hook 'coq-maybe-compile-buffer nil t))

(defun coq-shell-mode-config ()
  (setq
   proof-shell-cd-cmd coq-shell-cd
   proof-shell-filename-escapes '(("\\\\" . "\\\\") ("\""   . "\\\""))
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

                                        ; Coq has no global settings?
                                        ; (proof-assistant-settings-cmd))

   proof-shell-restart-cmd coq-shell-restart-cmd
   pg-subterm-anns-use-stack t
   )

  (coq-init-syntax-table)
  ; (holes-mode 1)  da: does the shell really need holes mode on?
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

; FIXME da: we should send this command only inside a proof,
; otherwise it gives an error message.  It should be on
; a different menu command.
;(defpacustom print-only-first-subgoal  nil
;  "Whether to just print the first subgoal in Coq."
;  :type 'boolean
;  :setting ("Focus. " . "Unfocus. "))


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

(defpacustom undo-depth 200
  "Depth of undo history.  Undo behaviour will break beyond this size."
  :type 'integer
  :setting "Set Undo %i . ")

(defpacustom time-commands nil
  "Whether to display timing information for each command."
  :type 'boolean)

(defpacustom undo-limit 100
  "Depth of undo history."
  :type 'integer
  :setting "Set Undo %i . ")

(defpacustom auto-compile-vos nil
  "Whether to automatically compile vos and track dependencies."
  :type 'boolean)

;; old adjustments:
;;  :eval (if coq-auto-compile-vos
;            (setq proof-shell-process-file
;                  coq-proof-shell-process-file
;                  proof-shell-inform-file-retracted-cmd
;                  coq-proof-shell-inform-file-retracted-cmd)
;          (setq proof-shell-inform-file-processed-cmd nil
;                proof-shell-process-file nil
;                proof-shell-inform-file-retracted-cmd nil)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Multiple file handling
;;
;; This is an imperfect attempt.  It really needs prover assistance.
;;
;; Experimental support for multiple files was first added
;; for Coq 6.X based on discussions at TYPES 2000 between DA and PC.
;; Updated and simplified for Coq 8, PG 3.5 (22.04.04) by DA.

;; First note that coq-shell-cd is sent whenever we activate scripting,
;; it extends the loadpath with the current directory.

;; When scripting is turned off, we compile the file to update the .vo.
(defun coq-maybe-compile-buffer ()
  "If the current buffer is completely processed, maybe compile it.
The attempt is made if `coq-auto-compile-vos' is non-nil.
This is a value for the `proof-deactivate-scripting-hook'."
  (if (and coq-auto-compile-vos
           (proof-locked-region-full-p)
           buffer-file-name)
      (progn
        ;; FIXME: in PG 4, this next step should be done inside
        ;; proof-register-possibly-new-processed-file.
        ;; NB: we might save dependent buffers too!
        (ignore-errors
          (proof-save-some-buffers (list (current-buffer))))
        ;; Now re-compile.
        ;; Coq users like Make, let's see if we have a Makefile
        ;; here and choose compile.
        (cond
         ((and (proof-try-require 'compile)
               compile-command
               (file-exists-p "Makefile"))
          ;; NB: compilation is run in the background in this case!
          (let ((compilation-read-command nil))
            (call-interactively 'compile)))
         (coq-compile-file-command
          (message "Compiling %s..." buffer-file-name)
          (shell-command
           ;; Could be run in the background here if we
           ;; added & to the end of the command.
           (format coq-compile-file-command buffer-file-name)))))))


;; Dependency management 1: when a buffer is retracted, we also
;; need to retract any children buffers.
;; To do that, we run coqdep on each of the processed files,
;; and see whether the buffer being retracted is an ancestor.

(defun coq-ancestors-of (filename)
  "Return ancestor .v files of RFILENAME.
This is based on the output of coqtop FILENAME.
Currently this doesn't take the loadpath into account."
  ;; FIXME: is there any way to bring in the load path here in coqdep?
  ;; We might use Coq's "Locate File string." command to help.
  (let* ((filedir   (file-name-directory filename))
         (cdline    (shell-command-to-string
                     (format "coqdep -I %s %s" filedir filename)))
         (matchdeps (string-match ": \\(.*\\)$" cdline))
         (deps      (and matchdeps
                         (split-string (match-string 1 cdline)))))
    (mapcar
     ;; normalise to include directories, defaulting
     ;; to same dir.  Change .vo -> v
     (lambda (file)
       (concat
        (if (file-name-directory file) "" filedir)
        (file-name-sans-extension file) ".v"))
     ;; first dep is vacuous: file itself
     (cdr-safe deps))))

;; FIXME: memoise here
(defun coq-all-ancestors-of (filename)
  "Return transitive closure of `coq-ancestors-of'."
  (let ((ancs   (coq-ancestors-of filename))
        all)
    (dolist (anc ancs)
      (setq all (union (cons anc
                             (coq-all-ancestors-of anc))
                       all
                       :test 'string-equal)))
    all))

(defun coq-process-require-command (span cmd)
  "Calculate the ancestors of a loaded file and lock them."
  ;; FIXME todo
  )

(defun coq-included-children (filename)
  "Return a list of children of FILENAME on `proof-included-files-list'."
  (let (children)
    (dolist (incf proof-included-files-list)
      ;; Compute all ancestors transitively: could be expensive
      ;; if we have a lot of included files with many ancestors.
      (let ((ancestors (coq-all-ancestors-of incf)))
        (if (member filename ancestors)
            (setq children (cons incf children)))))
    children))


;; Dependency management 2: when a "Require " is executed,
;; PG should lock all files whose .vo's are loaded.
;; This would be easy if Coq would output some handy
;; messages tracking dependencies in .vo's as it loads
;; those files.   But it doesn't.
;; FIXME: to do this we'll need to watch the
;; Require commands ourselves, and then *lock* their
;; ancestors. TBD.

(defun coq-process-file (rfilename)
  "Adjust the value of `proof-included-files-list' when processing RFILENAME."
  (if coq-auto-compile-vos
      (progn
        (add-to-list proof-included-files-list rfilename)
        ;; recursively call on ancestors: we hope coqdep doesn't give loop!
        (coq-process-file (coq-ancestors-of rfilename)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Pre-processing of input string  (PG 3.5)
;;

;; Remark: `action' and `string' are known by `proof-shell-insert-hook'
(defun coq-preprocessing ()
  (if coq-time-commands
      (with-no-warnings  ;; NB: dynamic scoping of `string'
        (setq string (concat "Time " string)))))

(add-hook 'proof-shell-insert-hook 'coq-preprocessing)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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


;;;;;;;;;;;;;;;;;;;;;
; Some smart insertion function
;;;;;;;;;;;;;;;;;;;;;;

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
      ((mods (completing-read "kind of module (tab to see list): " module-kinds-table))
       (s (read-string  "Name: "))
       (typkind (if (string-equal mods "Section")
                    "" ;; if not a section
                  (completing-read "kind of type (optional, tab to see list): "
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
      (holes-set-point-next-hole-destroy))
    )
  )

(defconst reqkinds-kinds-table
  '(("Require" 1) ("Require Export" 2) ("Import" 3))
  "Enumerates the different kinds of requiring a module.")


(defun coq-insert-requires ()
  "Insert requires to modules, iteratively."
  (interactive)
  (let* ((s)
         (reqkind
          (completing-read "Command (tab to see list, default Require Export) : "
                           reqkinds-kinds-table nil nil nil nil "Require Export"))
         )
    (setq s (read-string  "Name (empty to stop) : "))
    (while (not (string-equal s ""))
      (insert (format "%s %s.\n" reqkind s))
      (setq s (read-string  "Name (empty to stop) : ")))
    )
  )


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
        (error "Don't know what to intro. ")
      (insert intros)
      (indent-according-to-mode))))


(defun coq-insert-infoH-hook ()
  (with-no-warnings  ;; NB: dynamic scoping of `string'
    (setq string (concat "infoH " string))))

;; da: FIXME untested with new generic hybrid code: hope this still works
(defun coq-insert-as ()
  "Insert an \"as\" suffix to the next command with names given by \"infoH\"
tactical.  Based on idea mentioned in Coq reference manual."
  (interactive)
  (add-hook 'proof-shell-insert-hook 'coq-insert-infoH-hook)
  (proof-assert-next-command-interactive)
  (remove-hook 'proof-shell-insert-hook 'coq-insert-infoH-hook);as soone as possible
  (proof-shell-wait)
  (let
      ((str (string-match "<info type=\"infoH\">\\([^<]*\\)</info>"
                          proof-shell-last-response-output))
       (substr (match-string 1 proof-shell-last-response-output)))
    (coq-find-command-end-backward)
    (let ((inhibit-read-only t)) 
      (insert (concat " as " substr)))))


(defun coq-insert-match ()
  "Insert a match expression from a type name by Show Intros.
Based on idea mentioned in Coq reference manual. Also insert holes at insertion
positions."
  (interactive)
  (proof-shell-ready-prover)
  (let* ((cmd))
    (setq cmd (read-string "Build match for type:"))
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
           "\\[holes-set-point-next-hole-destroy] to jump to active hole.  \\[holes-short-doc] to see holes doc.")))))
          )))))



(defun coq-insert-tactic ()
  "Ask for a tactic name, with completion on a quasi-exhaustive list of coq
tactics and insert it at point.  Questions may be asked to the user."
  (interactive)
  (coq-insert-from-db coq-tactics-db "Tactic"))

(defun coq-insert-tactical ()
  "Ask for a tactical name, with completion on a quasi-exhaustive list of coq
tacticals and insert it at point.  Questions may be asked to the user."
  (interactive)
  (coq-insert-from-db coq-tacticals-db "Tactical"))

(defun coq-insert-command ()
  "Ask for a command name, with completion on a quasi-exhaustive list of coq
commands and insert it at point.  Questions may be asked to the user."
  (interactive)
  (coq-insert-from-db coq-commands-db "Command"))

(defun coq-insert-term ()
  "Ask for a term kind, with completion and insert it at point.  Questions may
be asked to the user."
  (interactive)
  (coq-insert-from-db coq-terms-db "Kind of term"))

(define-key coq-keymap [(control ?i)] 'coq-insert-intros)
(define-key coq-keymap [(control ?m)] 'coq-insert-match)
(define-key coq-keymap [(control ?()] 'coq-insert-section-or-module)
(define-key coq-keymap [(control ?))] 'coq-end-Section)
(define-key coq-keymap [(control ?s)] 'coq-Show)
(define-key coq-keymap [(control ?t)] 'coq-insert-tactic)
(define-key coq-keymap [(control ?T)] 'coq-insert-tactical)

(define-key coq-keymap [(control space)] 'coq-insert-term)
(define-key coq-keymap [(control return)] 'coq-insert-command)

(define-key coq-keymap [(control ?r)] 'coq-insert-requires)
(define-key coq-keymap [(control ?o)] 'coq-SearchIsos)

(define-key coq-keymap [(control ?p)] 'coq-Print)
(define-key coq-keymap [(control ?b)] 'coq-About)
(define-key coq-keymap [(control ?a)] 'coq-SearchAbout)
(define-key coq-keymap [(control ?c)] 'coq-Check)
(define-key coq-keymap [(control ?h)] 'coq-PrintHint)
(define-key coq-keymap [(control ?l)] 'coq-LocateConstant)
(define-key coq-keymap [(control ?n)] 'coq-LocateNotation)


(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?c)] 'coq-Check)
(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?p)] 'coq-Print)
(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?o)] 'coq-SearchIsos)
(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?b)] 'coq-About)
(define-key coq-goals-mode-map [(control ?c)(control ?a)(control ?a)] 'coq-searchabout)
; window auto-resize makes this bug sometimes. Too bad!.
;(define-key coq-response-mode-map [(control ?c)(control ?a)(control ?c)] 'coq-Check)

;;;;;;;;;;;;;;;;;;;;;;;;
;; error handling
;;;;;;;;;;;;;;;;;;;;;;;;


(defvar last-coq-error-location nil
  "The last error message seen by `coq-get-last-error-location' and
`coq-highlight-error'.")


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
    (with-current-buffer proof-response-buffer
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
            (let ((bytes (encode-coding-string text 'utf-8-unix)))
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
  (let ((mtch (coq-get-last-error-location parseresp clean)))
    (when mtch
      (let ((pos (car mtch))
            (lgth (cadr mtch)))
        (set-buffer proof-script-buffer)
        (goto-char (+ (proof-unprocessed-begin) 1))
        (coq-find-real-start)

        ; utf8 adaptation is made in coq-get-last-error-location above
        (goto-char (+ (point) pos))
        (let* ((sp (span-make (point) (+(point) lgth))))
          (set-span-face sp 'proof-warning-face)
          (unwind-protect
              (sit-for 5) ;; da: this was 20 but seemed obnoxiously long?
            (span-delete sp)))))))

(defvar coq-allow-highlight-error t
  "Internal variable. Do not use as configuration variable.")

;; if a command is sent to coq without being in the script, then don't
;; higilight the error. Remark: `action' and `string' are known by
;; `proof-shell-insert-hook', but not by
;; `proof-shell-handle-error-or-interrupt-hook'
(defun coq-decide-highlight-error ()
  (setq coq-allow-highlight-error
        (not (with-no-warnings ;; Dynamic scope of `action'
               (eq action 'proof-done-invisible)))))

(defun coq-highlight-error-hook ()
  (if coq-allow-highlight-error (coq-highlight-error t t)))

;; We need this two hooks to highlight only when scripting
(add-hook 'proof-shell-handle-error-or-interrupt-hook 'coq-highlight-error-hook t)
(add-hook 'proof-shell-insert-hook 'coq-decide-highlight-error t)



;; What follows allows to scroll response buffer to maximize display of first
;; goal
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
  (let* ((curwin (selected-window))
         (goalbuf (get-buffer-window proof-goals-buffer)))
    (if (eq goalbuf nil) ()
      (select-window goalbuf)
      (search-forward-regexp "subgoal 2\\|\\'"); find snd goal or buffer end
      (beginning-of-line)
      (ignore-errors (search-backward-regexp "\\S-")) ; find something else than a space
      (recenter (- 1)) ; put it at bottom og window
      (beginning-of-line)
      (select-window curwin)
      )))

(defvar coq-modeline-string2 " SUBGOALS* ")
(defvar coq-modeline-string1 " SUBGOAL* ")
(defvar coq-modeline-string0 " Scripting *")
(defun coq-build-subgoals-string (n)
  (concat coq-modeline-string0 (int-to-string n)
          (if (> n 1) coq-modeline-string2
            coq-modeline-string1)))

(defun coq-update-minor-mode-alist ()
  "Modify `minor-mode-alist' to display the number of subgoals in the modeline."
  (save-window-excursion ; switch to buffer even if not visible
    (switch-to-buffer proof-goals-buffer)
    (let* ((nbgoals (string-to-number (first-word-of-buffer)))
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
;;   End: ***

;;; coq.el ends here
