;; coq.el Major mode for Coq proof assistant
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Author: Healfdene Goguen
;; Maintainer: Pierre Courtieu <courtieu@lri.fr>

;; $Id$ 

(require 'proof)
(require 'coq-syntax)

;; Configuration

(setq tags-always-exact t) ; Tags is unusable with Coq library otherwise:

(defun coq-library-directory () 
  (let ((c (substring (shell-command-to-string "coqtop -where") 0 -1 )))
    (if (string-match c "not found")
	  "/usr/local/lib/coq"
      c)))


(defcustom coq-tags (concat (coq-library-directory) "/theories/TAGS")
  "the default TAGS table for the Coq library"
  :type 'string
  :group 'coq)

(defconst coq-interrupt-regexp "User Interrupt."
  "Regexp corresponding to an interrupt")

(defcustom coq-default-undo-limit 100
  "Maximum number of Undo's possible when doing a proof."
  :type 'number
  :group 'coq)

;; ----- web documentation

(defcustom coq-www-home-page "http://coq.inria.fr/"
  "Coq home page URL."
  :type 'string
  :group 'coq)

;; ----- coq specific menu

(defpgdefault menu-entries
  '(["Print..." coq-Print t]
    ["Check..." coq-Check t]
    ["Hints" coq-PrintHint t]
    ["Intros..." coq-Intros t]
    ["Show ith goal..." coq-Show t]
    ["Apply"  coq-Apply t]
    ["Search isos/pattern..." coq-SearchIsos t]
    ["Begin Section..." coq-begin-Section t]
    ["End Section" coq-end-Section t]
    ["Compile" coq-Compile t]))


;; ----- coq-shell configuration options

(defcustom coq-prog-name "coqtop -emacs"
  "*Name of program to run as Coq."
  :type 'string
  :group 'coq)

;; Command to initialize the Coq Proof Assistant
(defconst coq-shell-init-cmd 
  (format "Set Undo %s. " coq-default-undo-limit))


;;Pierre: we will have both versions V6 and V7 during a while
;;        the test with "coqtop -v" can be skipped if the variable 
;;        coq-version-is-V7 is already set (usefull for people 
;;        dealing with several version of coq)
;; We also have coq-version-is-V74, to deal with the new module system
(cond
 ((boundp 'coq-version-is-V74) (setq coq-version-is-V7 t))
 ((boundp 'coq-version-is-V7) (setq coq-version-is-V74 nil))
 (t 
  (let* ((str (shell-command-to-string (concat coq-prog-name " -v")))
         (x (string-match "version \\([.0-9]*\\)" str))
         (num (match-string 1 str)))
    (cond
     ((string-match num "\\<6.")
      (message "coq is V6") (setq coq-version-is-V7 nil) (setq coq-version-is-V74 nil))
     ((or (string-match num "\\<7.0") (string-match num "\\<7.1") 
          (string-match num "\\<7.2") (string-match num "\\<7.3")) 
      (message "coq is V7 =< 7.3") 
      (setq coq-version-is-V7 t) (setq coq-version-is-V74 nil))
      ;default: 7.3.1 and above ---> 7.4 
     (t (message "coq is => V7.3.1")
        (setq coq-version-is-V7 t) (setq coq-version-is-V74 t))))))

;; Command to reset the Coq Proof Assistant
;; Pierre: added Impl... because of a bug of Coq until V6.3
;; (included). The bug is already fixed in the next version (V7). So
;; we will backtrack this someday.
(defconst coq-shell-restart-cmd 
  "Reset Initial.\n Implicit Arguments Off. ")

(defvar coq-shell-prompt-pattern (concat "^" proof-id " < ")
  "*The prompt pattern for the inferior shell running coq.")

;; FIXME da: this was disabled (set to nil) -- why?
(defvar coq-shell-cd "Cd \"%s\". "
  "*Command of the inferior process to change the directory.") 

(defvar coq-shell-abort-goal-regexp "Current goal aborted"
  "*Regexp indicating that the current goal has been abandoned.")

(defvar coq-shell-proof-completed-regexp "Subtree proved!"
  "*Regular expression indicating that the proof has been completed.")

(defvar coq-goal-regexp
  "\\(============================\\)\\|\\(subgoal [0-9]+ is:\\)\n")


;; ----- outline

(defvar coq-outline-regexp
  (concat "(\\*\\|" (proof-ids-to-regexp 
	   '(
"Tactic" "Axiom" "Parameter" "Parameters" "Variable" "Variables" "Syntax" "Grammar" "Syntactic" "Load" "Require" "Import" "Hint" "Hints" "Hypothesis" "Correctness" "Module" "Section" "Chapter" "Goal" "Lemma" "Theorem" "Fact" "Remark" "Record" "Inductive" "Mutual" "Definition" "Fixpoint" "Save" "Qed" "Defined" "End" "Coercion"))))

(defvar coq-outline-heading-end-regexp "\\*\)\n\\|\\.\n")

(defvar coq-shell-outline-regexp coq-goal-regexp)
(defvar coq-shell-outline-heading-end-regexp coq-goal-regexp)

(defconst coq-kill-goal-command "Abort. ")
(defconst coq-forget-id-command "Reset %s. ")
(defconst coq-back-n-command "Back %s. ") ; Pierre: added 



(defconst coq-state-changing-tactics-regexp 
  (proof-ids-to-regexp coq-state-changing-tactics))
(defconst coq-state-preserving-tactics-regexp 
  (proof-ids-to-regexp coq-state-preserving-tactics))
(defconst coq-tactics-regexp
  (proof-ids-to-regexp coq-tactics))
(defconst coq-state-changing-commands-regexp
  (proof-ids-to-regexp coq-keywords-state-changing-commands))
(defconst coq-state-preserving-commands-regexp 
  (proof-ids-to-regexp coq-keywords-state-preserving-commands))
(defvar coq-retractable-instruct-regexp 
  (proof-ids-to-regexp coq-retractable-instruct))
(defvar coq-non-retractable-instruct-regexp
  (proof-ids-to-regexp coq-non-retractable-instruct))

(defvar coq-keywords-section
  (cond 
   (coq-version-is-V74 '("Section" "Module\\-+Type" "Module"))
   (t '("Section"))))

(defvar coq-section-regexp 
;  (proof-ids-to-regexp coq-keywords-section)
  "\\(\\<Section\\>\\|\\<Module\\>\\-+\\<Type\\>\\|\\<Module\\>\\)"
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-and-compile 
  (define-derived-mode coq-shell-mode proof-shell-mode
    "coq-shell" nil
    (coq-shell-mode-config)))
  
(eval-and-compile 
  (define-derived-mode coq-response-mode proof-response-mode
  "CoqResp" nil
    (coq-response-config)))
 
(eval-and-compile
  (define-derived-mode coq-mode proof-mode
   "coq" nil
   (coq-mode-config)))

(eval-and-compile
  (define-derived-mode coq-goals-mode proof-goals-mode
    "CoqGoals" nil
    (coq-goals-mode-config)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's coq specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-set-undo-limit (undos)
  (proof-shell-invisible-command (format "Set Undo %s. " undos)))

;;
;; FIXME Papageno 05/1999: must take sections in account.
;;
;; da: have now combined count-undos and find-and-forget, they're the
;; same now we deal with nested proofs and send general sequence
;; "Abort. ... Abort. Back n. Undo n."
;;

(defconst coq-keywords-decl-defn-regexp
  (proof-ids-to-regexp (append coq-keywords-decl coq-keywords-defn))
  "Declaration and definition regexp.")

;; FIXME da: this one function breaks the nice configuration of Proof General:
;; would like to have proof-goal-regexp instead.
;; Unfortunately Coq allows "Definition" and friends to perhaps have a goal, 
;; so it appears more difficult than just a proof-goal-regexp setting.
;; Future improvement may simply to be allow a function value for
;; proof-goal-regexp.

(defun coq-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (and (proof-string-match coq-goal-command-regexp str)
       (not (proof-string-match "Definition.*:=" str))
		 (not (proof-string-match "Recursive Definition" str))
       ;; da: 3.4 test: do not exclude Lemma: we want goal-command-p to
       ;; succeed for nested goals too now.
       ;; (should we also exclude Definition?)
       (not (proof-string-match "Lemma.*:=" str))))
;; ))


; Pierre: This is a try, for use in find-and-forget. It seems to work but 
; is it correct with respect to the asynchronous communication between Coq 
; and emacs?  
; DA: should be okay, communication is not as asynchronous as you think
(defun coq-proof-mode-p ()
  "Allows to know if we are currentlly in proof mode. 
Look at the last line of the *coq* buffer to see if the prompt is the
toplevel \"Coq <\". Returns nil if yes. This assumes that no
\"Resume\" or \"Suspend\" command has been used."
  (not (string-match "^Coq < " proof-shell-last-prompt)))


;; Pierre: May 29 2002 added a "Back n. " command in order to
;; synchronize more accurately.
 
;; DA: rewrote to combine behaviour with count-undos, to work with
;; nested proofs.




(defun coq-find-and-forget (span)
  (let (str ans (naborts 0) (nbacks 0) (nundos 0))
    (while (and span (not ans))
      (setq str (span-property span 'cmd))
      (cond
       ((eq (span-property span 'type) 'comment))
       
       ;; FIXME: combine with coq-keywords-decl-defn-regexp case below?
       ;; [ Maybe not: Section is being treated as a _goal_ command
       ;;   now, so this test has to appear before the goalsave ]       
       ((proof-string-match 
         (concat coq-section-regexp 
                 "\\s-+\\(" proof-id "\\)\\(\\s-*\\(" proof-id "\\)\\)?") str)
        (unless (eq (span-property span 'type) 'goalsave)
          ;; If we're resetting to beginning of a section from
          ;; inside, need to fix the nesting depth.
          ;; FIXME: this is not good enough: the scanning loop
          ;; exits immediately but Reset has implicit Aborts
          ;; which are not being counted here.  Really
          ;; we need to set the "master reset" command which
          ;; subsumes the others, but still count the depth.
          (decf proof-nesting-depth))
        (if (equal (match-string 2 str) "Type") ;Module Type id: take the third word
            (progn 
              (setq ans (format coq-forget-id-command (match-string 5 str))))
          (setq ans (format coq-forget-id-command (match-string 2 str))))
        )
       ((eq (span-property span 'type) 'goalsave)
        ;; Note da 6.10.99: in Lego and Isabelle, it's trivial to forget an
        ;; unnamed theorem.  Coq really does use the identifier
        ;; "Unnamed_thm", though!  So we don't need this test:
        ;;(unless (eq (span-property span 'name) proof-unnamed-theorem-name)

        ;; da: try using just Back since "Reset" causes loss of proof
        ;; state.
        ;; (format coq-forget-id-command (span-property span 'name)))
        (if (span-property span 'nestedundos) 
            (setq nbacks (+ 1 nbacks (span-property span 'nestedundos)))))
       
       ;; Unsaved goal commands: each time we hit one of these
       ;; we need to issue Abort to drop the proof state.
       ((coq-goal-command-p str)
        ;;Todo Hack: if Definition:foo. inside a "Module Type": it is
        ;;not a proof start!!
        ;(if (and (proof-string-match "Definition\\-+:[^=]?" str)
        ;         (inside-module-type))
        ;  (incf nfalseaborts))
        (incf naborts))
       
       ;; If we are already outside a proof, issue a Reset.
       ;; [ improvement would be to see if the undoing
       ;;   will take us outside a proof, and use the first
       ;;   Reset found if so: but this is tricky to co-ordinate
       ;;   with the number of Backs, perhaps? ]
       ((and 
         (not (coq-proof-mode-p));; (eq proof-nesting-depth 0)
         (proof-string-match 
          (concat "\\`\\(" coq-keywords-decl-defn-regexp "\\)\\s-*\\(" 
                  proof-id 
                  ;; Section .. End Section should be atomic!
                  "\\)\\s-*[\\[,:.]") str))
        (setq ans (format coq-forget-id-command (match-string 2 str))))

       ;; FIXME: combine with coq-keywords-decl-defn-regexp case above?
       ;; If it's not a goal but it contains "Definition" then it's a
       ;; declaration  [ da: is this not covered by above case??? ]
       ((and (not (coq-proof-mode-p));; (eq proof-nesting-depth 0)
             (proof-string-match
              (concat "Definition\\s-+\\(" proof-id "\\)\\s-*") str))
        (setq ans (format coq-forget-id-command (match-string 2 str))))
		 
       ;; Outside a proof: cannot be a tactic, if unknown: do back 
       ;; (we may decide otherwise, it is false anyhow, use elisp 
       ;; vars instead for the perfect thing).
       ((and (not (coq-proof-mode-p))
             (not (proof-string-match 
                   (concat "\\`\\(" 
                           coq-state-preserving-commands-regexp
                           "\\)")
                   str)))
        (incf nbacks))

       ;; inside a proof: if known command then back or nothing (depending 
       ;;                 on the command), 
       ;; if known "need not undo tactic" then nothing
       ;; otherwise : undo (unknown tactics are considered needing undo, 
       ;;                    which is ok at 99%, use elisp vars for the 
       ;;                    1% remaining).
       ;; no undo if abort
       ((coq-proof-mode-p)
        (cond
         ((proof-string-match 
           (concat "\\`\\(" coq-state-changing-commands-regexp "\\)")
           str)
          (incf nbacks))
         ((and (eq 0 naborts)
               (not (proof-string-match 
                     (concat "\\`\\(" coq-state-preserving-commands-regexp "\\)")
                     str))
               (not (proof-string-match 
                     (concat "\\`\\(" coq-state-preserving-tactics-regexp "\\)")
                     str)))
          (incf nundos))
         ))
       )
      (setq span (next-span span 'type)))
    
    ;; Now adjust proof-nesting depth according to the
    ;; number of proofs we've passed out of.
    ;; FIXME: really this adjustment should be on the
    ;; successful completion of the Abort commands, as
    ;; a callback.
    (setq proof-nesting-depth (- proof-nesting-depth naborts))

    (setq ans
          (concat
           (if (stringp ans) ans)
           (if (> naborts 0)
               ;; ugly, but blame Coq
               (let ((aborts "Abort. "))
                 (while (> (decf naborts) 0)
                   (setq aborts (concat "Abort. " aborts)))
                 aborts))
           (if (> nbacks 0)
               (concat "Back " (int-to-string nbacks) ". "))
           (if (> nundos 0) 
               (concat "Undo " (int-to-string nundos) ". "))))

    (if (null ans) 
        proof-no-command;; FIXME: this is an error really (assert nil)
      ans)))
  

(defvar coq-current-goal 1
  "Last goal that emacs looked at.")

(defun coq-goal-hyp ()
  (cond 
   ((looking-at "============================\n")
    (goto-char (match-end 0))
    (cons 'goal (int-to-string coq-current-goal)))
   ((looking-at "subgoal \\([0-9]+\\) is:\n")
    (goto-char (match-end 0))
    (cons 'goal (match-string 1))
    (setq coq-current-goal (string-to-int (match-string 1))))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))

(defun coq-state-preserving-p (cmd)
  (not (proof-string-match coq-retractable-instruct-regexp cmd)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to coq                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-SearchIsos ()
  "Search a term whose type is isomorphic to given type
This is specific to coq-mode."
  (interactive)
  (let (cmd)
    (proof-shell-ready-prover) 
    (setq cmd (read-string 
	       (if coq-version-is-V7 "SearchPattern: " "SearchIsos: ") 
	       nil 'proof-minibuffer-history))
    (proof-shell-invisible-command
     (format (if coq-version-is-V7 "SearchPattern %s. "
	       "SearchIsos %s. ") cmd))))


(defun coq-guess-or-ask-for-string (s)
  (let ((guess
			(if (region-exists-p) 
				 (buffer-substring-no-properties (region-beginning) (region-end))
				 (symbol-near-point))))
	 (read-string 
	  (if guess (concat s " (" guess "):")(concat s ":"))
	 nil 'proof-minibuffer-history guess))
  )

(defun coq-Print ()
  "Ask for an ident and print the corresponding term"
  (interactive)
  (let (cmd)
    (proof-shell-ready-prover) 
    (setq cmd (coq-guess-or-ask-for-string "Print"))
    (proof-shell-invisible-command
     (format "Print %s. " cmd))))

(defun coq-Check ()
  "Ask for a term and print its type"
  (interactive)
  (let (cmd)
    (proof-shell-ready-prover) 
    (setq cmd (coq-guess-or-ask-for-string "Check"))
    (proof-shell-invisible-command
     (format "Check %s. " cmd))))

(defun coq-Show ()
  "Ask for a number i and show the ith goal"
  (interactive)
  (let (cmd)
    (proof-shell-ready-prover) 
    (setq cmd (read-string "Show Goal number: " nil 'proof-minibuffer-history))
    (proof-shell-invisible-command
     (format "Show %s. " cmd))))

(defun coq-PrintHint ()
  "Print all hints applicable to the current goal"
  (interactive)
  (proof-shell-invisible-command "Print Hint. "))


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

(defun coq-Compile ()
  "compiles current buffer"
  (interactive)
  (let* ((n (buffer-name))
	 (l (string-match ".v" n)))
    (compile (concat "make " (substring n 0 l) ".vo"))))

(proof-defshortcut coq-Intros        "Intros "  [(control ?i)])
(proof-defshortcut coq-Apply         "Apply "   [(control ?a)])
(proof-defshortcut coq-begin-Section "Section " [(control ?s)])

(define-key coq-keymap [(control ?e)] 'coq-end-Section)
(define-key coq-keymap [(control ?m)] 'coq-Compile)
(define-key coq-keymap [(control ?o)] 'coq-SearchIsos)
(define-key coq-keymap [(control ?p)] 'coq-Print)
(define-key coq-keymap [(control ?c)] 'coq-Check)
(define-key coq-keymap [(control ?h)] 'coq-PrintHint)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Indentation                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; FIXME mmw: code disabled; Is the new indentation scheme general
;; enough to handle Coq as well?

;;; "Case" is represented by 'c' on the stack, and
;;; "CoInductive" is represented by 'C'.
;(defun coq-stack-to-indent (stack)
;  (cond
;   ((null stack) 0)
;   ((null (car (car stack)))
;    (nth 1 (car stack)))
;   (t (let ((col (save-excursion
;		   (goto-char (nth 1 (car stack)))
;		   (current-column))))
;	(cond
;	 ((eq (car (car stack)) ?c)
;	  (save-excursion (move-to-column (current-indentation))
;			  (cond 
;			   ((eq (char-after (point)) ?|) (+ col 3))
;			   ((proof-looking-at "end") col)
;			   (t (+ col 5)))))	  
;	 ((or (eq (car (car stack)) ?I) (eq (car (car stack)) ?C))
;	  (+ col (if (eq ?| (save-excursion 
;			      (move-to-column (current-indentation))
;			      (char-after (point)))) 2 4)))
;	 (t (1+ col)))))))
;
;(defun coq-parse-indent (c stack)
;  (cond
;   ((eq c ?C)
;    (cond ((proof-looking-at "Case")
;	   (cons (list ?c (point)) stack))
;	  ((proof-looking-at "CoInductive")
;	   (forward-char (length "CoInductive"))
;	   (cons (list c (- (point) (length "CoInductive"))) stack))
;	  (t stack)))
;   ((and (eq c ?e) (proof-looking-at "end") (eq (car (car stack)) ?c))
;    (cdr stack))
;
;   ((and (eq c ?I) (proof-looking-at "Inductive"))
;    (forward-char (length "Inductive"))
;    (cons (list c (- (point) (length "Inductive"))) stack))
;
;   ((and (eq c ?.) (or (eq (car (car stack)) ?I) (eq (car (car stack)) ?C)))
;    (cdr stack))
;
;   (t stack)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;    To guess the command line options   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun coq-guess-command-line (filename)
  "Guess the right command line options to compile FILENAME using `make -n'"
  (let ((dir (file-name-directory filename)))
    (if (file-exists-p (concat dir "Makefile"))
	(let* 
	    ((compiled-file (concat (substring 
				     filename 0 
				     (string-match ".v$" filename)) ".vo"))
	     (command (shell-command-to-string 
		       (concat  "cd " dir ";"
				"gmake -n -W " filename " " compiled-file
				"| sed s/coqc/coqtop/"))))
	  (concat 
	   (substring command 0 (string-match " [^ ]*$" command))
	   " -emacs"))
      coq-prog-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Coq shell startup and exit hooks                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-pre-shell-start ()
  (setq proof-prog-name coq-prog-name)
  (setq proof-mode-for-shell    'coq-shell-mode)
  (setq proof-mode-for-goals    'coq-goals-mode)
  (setq proof-mode-for-response 'coq-response-mode)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-mode-config ()

  (setq proof-terminal-char ?\.)
  (setq proof-script-command-end-regexp   
	(if coq-version-is-V7 "[.]\\([ \t\n\r]\\)\\|[.]\\'" "[.]"))
  (setq proof-script-comment-start "(*")
  (setq proof-script-comment-end "*)")
  (setq proof-unnamed-theorem-name "Unnamed_thm") ; Coq's default name

  (setq proof-assistant-home-page coq-www-home-page)

  (setq proof-mode-for-script 'coq-mode)

  (setq proof-guess-command-line 'coq-guess-command-line)

  ;; Commands sent to proof engine
  (setq proof-showproof-command "Show. "
	proof-context-command "Print All. "
	proof-goal-command "Goal %s. "
	proof-save-command "Save %s. "
	proof-find-theorems-command "Search %s. ")
;; FIXME da: Does Coq have a help or about command?
;;	proof-info-command "Help"

;; 3.4: this is no longer used: setting to nil
;; enforces use of find-and-forget always.
  (setq proof-kill-goal-command nil)

  (setq proof-goal-command-p 'coq-goal-command-p
	proof-find-and-forget-fn 'coq-find-and-forget
        pg-topterm-goalhyp-fn 'coq-goal-hyp
	proof-state-preserving-p 'coq-state-preserving-p)

  (setq proof-save-command-regexp coq-save-command-regexp
	proof-save-with-hole-regexp coq-save-with-hole-regexp
	proof-goal-with-hole-regexp coq-goal-with-hole-regexp
	proof-nested-undo-regexp coq-state-changing-commands-regexp)
  
  (setq	
   proof-indent-close-offset -1
   proof-indent-any-regexp
   (proof-regexp-alt (proof-ids-to-regexp
		      (append (list "Cases" "end") coq-keywords)) "\\s(" "\\s)")
   proof-indent-enclose-regexp "|"
   proof-indent-open-regexp
   (proof-regexp-alt (proof-ids-to-regexp '("Cases")) "\\s(")
   proof-indent-close-regexp
   (proof-regexp-alt (proof-ids-to-regexp '("end")) "\\s)"))

  ;; span menu 
  (setq
   proof-script-span-context-menu-extensions 'coq-create-span-menu)

  ;; (setq proof-auto-multiple-files t)	; until Coq has real support
  ;; da: Experimental support for multiple files based on discussions
  ;; at TYPES 2000. 
  ;; (Pierre, please fix this as Coq users would like, and for Coq V7 !)
  (setq coq-proof-shell-inform-file-processed-cmd
	"Reset Initial. Compile Module %m. ")
  ;; FIXME da: Coq is rather quiet when reading files with "Load <foo>."
  ;; and sometimes even Require seems quiet?  PG would like some guarantees
  ;; that messages are issued.  Also, the code to guess the complete file
  ;; name is flaky, would be better if Coq displayed full path info for PG.
  (setq coq-proof-shell-process-file 
	;; FIXME da: Coq output Reinterning message should not
	;; be suppressed by "Begin Silent" for PG, and should be
	;; marked by eager annotation (special char).
	;; For Coq 7, we should get rid of 8 bit chars in PG, too.
	(cons "Reinterning \\(.+\\)\\.\\.\\.done"
	      (lambda (str)
		(let*
		    ((modname (match-string 1 str))
		     ;; FIXME: next lines will return a directory but maybe
		     ;; not right one if proof-script-buffer happens to be nil!
		     (buf     (or proof-script-buffer
				  proof-previous-script-buffer))
		     (dir     (if (buffer-live-p buf)
				  (with-current-buffer buf
				    default-directory)
				;; This next guess is pretty hopeless.
				default-directory)))
		  (message "%s%s.v" dir modname)
		  (format "%s%s.v" dir modname)))))

  (setq coq-proof-shell-inform-file-retracted-cmd
	;; da: This is a HORRIBLE fragile hack!  Instead of issuing a
	;; command to the prover we have to run a "coqdep" command to
	;; find out the dependencies.
	(lambda (fname) 
	  (let*
	      ;; Assume buffer is in correct directory, assume current directory
	      ;; is writeable, assume we have GNU make, etc, etc.  
	      ;; I hope Coq V7 will provide this operation for us as
	      ;; a builtin (it should print out a series of messages which
	      ;; are matched by proof-shell-retract-files-regexp, one for
	      ;; each dependency).
	      ;; [In fact, I think this is what should happen when 
	      ;; Require is undone]
	      ((depstr 
		(substring (shell-command-to-string
			    (concat
			     "coqdep *.v | grep " 
			     (file-name-nondirectory 
			      (file-name-sans-extension fname)) ".v"
			      " | awk '{print $1}' | sed 's/.vo:/.v/'")) 0 -1))
	       (deps (split-string depstr))
               (current-included proof-included-files-list))
		;; Now hack the proof-included-files-list to remove the
		;; dependencies of the retracted file and remove the 
		;; locked regions
		;; FIXME: this is too low-level delving in PG. Should
		;; do with proof-shell-retract-files-regexp really.
	        (mapcar (lambda (dep) 
		   (setq proof-included-files-list 
			   (delete (file-truename dep) 
				    proof-included-files-list)))
	           deps)
		(proof-restart-buffers
		 (proof-files-to-buffers
		  (set-difference current-included
			  proof-included-files-list)))
		;; Return a comment thingy inserted into the shell
		;; buffer to help debugging.
		(format "Print (* Proof General ran coqdep command for %s, result: %s.  Removed files: %s *)" fname depstr deps))))


  ;;Coq V7 changes this 
  (setq proof-shell-start-silent-cmd 
	(if coq-version-is-V7 "Set Silent. "   "Begin Silent. ")
	proof-shell-stop-silent-cmd  
	(if coq-version-is-V7 "Unset Silent. " "End Silent. "))
;  (setq proof-shell-start-silent-cmd "Begin Silent. "
;	proof-shell-stop-silent-cmd  "End Silent. ")

  (coq-init-syntax-table)

;; font-lock

  (setq font-lock-keywords coq-font-lock-keywords-1)

  (proof-config-done)

;; outline
  
  (make-local-variable 'outline-regexp)
  (setq outline-regexp coq-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp coq-outline-heading-end-regexp)

;; tags
  (and (boundp 'tag-table-alist)
       (setq tag-table-alist
	     (append '(("\\.v$" . coq-tags)
		       ("coq"  . coq-tags))
		     tag-table-alist)))

  (setq blink-matching-paren-dont-ignore-comments t)

;; hooks and callbacks
  
  (add-hook 'proof-pre-shell-start-hook 'coq-pre-shell-start nil t))
  


(defun coq-shell-mode-config ()
  (setq 
   proof-shell-prompt-pattern coq-shell-prompt-pattern
   proof-shell-cd-cmd coq-shell-cd
   proof-shell-filename-escapes '(("\\\\" . "\\\\") ("\""   . "\\\""))
   proof-shell-abort-goal-regexp coq-shell-abort-goal-regexp
   proof-shell-proof-completed-regexp coq-shell-proof-completed-regexp
   proof-shell-error-regexp coq-error-regexp
   proof-shell-interrupt-regexp coq-interrupt-regexp
   proof-shell-assumption-regexp coq-id
   pg-subterm-first-special-char ?\360
   proof-shell-wakeup-char ?\371 ; done: prompt
   ;; The next three represent path annotation information
   pg-subterm-start-char ?\372 ; not done
   pg-subterm-sep-char ?\373 ; not done
   pg-subterm-end-char ?\374 ; not done
   pg-topterm-char ?\375 ; done
   proof-shell-eager-annotation-start "\376\\|\\[Reinterning"
   proof-shell-eager-annotation-start-length 12
   proof-shell-eager-annotation-end "\377\\|done\\]" ; done
   proof-shell-annotated-prompt-regexp
   (concat proof-shell-prompt-pattern
	   (char-to-string proof-shell-wakeup-char)) ; done
   proof-shell-result-start "\372 Pbp result \373"
   proof-shell-result-end "\372 End Pbp result \373"
   proof-shell-start-goals-regexp "[0-9]+ subgoals?"
   proof-shell-end-goals-regexp proof-shell-annotated-prompt-regexp
   proof-shell-init-cmd  ; (concat
			 coq-shell-init-cmd
	                 ; Coq has no global settings?
			 ; (proof-assistant-settings-cmd))
   proof-shell-restart-cmd coq-shell-restart-cmd
   pg-subterm-anns-use-stack t)
  
  (coq-init-syntax-table)
  (setq font-lock-keywords coq-font-lock-keywords-1)

  (proof-shell-config-done))

(defun coq-goals-mode-config ()
  (setq pg-goals-change-goal "Show %s. ")
  (setq pg-goals-error-regexp coq-error-regexp)
  (coq-init-syntax-table)
  (setq font-lock-keywords coq-font-lock-keywords-1)
  (proof-goals-config-done))

(defun coq-response-config ()
   (coq-init-syntax-table)
   (setq font-lock-keywords coq-font-lock-keywords-1)
   (proof-response-config-done))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Flags and other settings for Coq.
;;

;; da: neither of these work very well.
;; I think "time" must just be for special search isos top level,
;; and "Focus" on works during a proof, so sending the setting
;; at the start of a session is wrong.

;(defpacustom time-search-isos  nil
;  "Whether to display timing of SearchIsos in Coq."
;  :type 'boolean
;  :setting ("Time. " . "Untime. "))

(defpacustom print-only-first-subgoal  nil
  "Whether to just print the first subgoal in Coq."
  :type 'boolean
  :setting ("Focus. " . "Unfocus. "))

(defpacustom auto-compile-vos nil
  "Whether to automatically compile vos and track dependencies."
  :type 'boolean
  :eval (if coq-auto-compile-vos
	    (setq proof-shell-inform-file-processed-cmd 
		  coq-proof-shell-inform-file-processed-cmd
		  proof-shell-process-file
		  coq-proof-shell-process-file
		  proof-shell-inform-file-retracted-cmd
		  coq-proof-shell-inform-file-retracted-cmd)
	  (setq proof-shell-inform-file-processed-cmd nil
		proof-shell-process-file nil
		proof-shell-inform-file-retracted-cmd nil)))

(provide 'coq)

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

;; da: message to Pierre: I just put these in as examples,
;; maybe you can suggest some better commands to use on
;; `thm'.  (Check maybe not much use since appears before
;; in the buffer anyway)
(defun coq-create-span-menu (span idiom name)
  (if (string-equal idiom "proof")
      (let ((thm (span-property span 'name)))
        (list ;(vector
              ; "Check"
              ; `(proof-shell-invisible-command 
              ;   ,(format "Check %s." thm)))
              (vector
               "Print Proof"
               `(proof-shell-invisible-command 
                 ,(format "Print Proof %s." thm)))))))

;;;   Local Variables: ***
;;;   tab-width:2 ***
;;;   indent-tabs-mode:nil ***
;;;   End: ***


