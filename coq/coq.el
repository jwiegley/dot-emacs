;; coq.el Major mode for Coq proof assistant
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Author: Healfdene Goguen
;; Maintainer: Pierre Courtieu <courtieu@lri.fr>

;; $Id$ 

(require 'proof-script)
(require 'coq-syntax)

;; Spans are our abstraction of extents/overlays.
(eval-and-compile
  (cond ((fboundp 'make-extent) (require 'span-extent))
	((fboundp 'make-overlay) (require 'span-overlay))))

(eval-and-compile
  (mapcar (lambda (f) (autoload f "proof-shell"))
	    '(proof-goals-mode proof-shell-config-done))) 

; Configuration

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

(proof-defass-default menu-entries
  '(["Intros" coq-Intros]
    ["Apply"  coq-Apply]
    ["Search isos" coq-SearchIsos]
    ["Begin Section" coq-begin-Section]
    ["End Section" coq-end-Section]
    ["Compile" coq-Compile]))


;; ----- coq-shell configuration options

(defcustom coq-prog-name "coqtop -emacs"
  "*Name of program to run as Coq."
  :type 'string
  :group 'coq)

;; Command to initialize the Coq Proof Assistant
(defconst coq-shell-init-cmd 
  (format "Set Undo %s" coq-default-undo-limit))

;; Command to reset the Coq Proof Assistant
(defconst coq-shell-restart-cmd 
  "Reset Initial.")

(defvar coq-shell-prompt-pattern (concat "^" proof-id " < ")
  "*The prompt pattern for the inferior shell running coq.")

;; FIXME da: this was disabled (set to nil) -- why?
(defvar coq-shell-cd "Cd \"%s\""
  "*Command of the inferior process to change the directory.") 

(defvar coq-shell-abort-goal-regexp "Current goal aborted"
  "*Regexp indicating that the current goal has been abandoned.")

(defvar coq-shell-proof-completed-regexp "Subtree proved!"
  "*Regular expression indicating that the proof has been completed.")

(defvar coq-goal-regexp
  "\\(============================\\)\\|\\(subgoal [0-9]+ is:\\)\n")

;; ----- outline

(defvar coq-outline-regexp
  (proof-ids-to-regexp 
	   '("Correctness" "Section" "Chapter" "Goal" "Lemma" "Theorem" "Fact"
	   "Remark" "Record" "Inductive" "Definition")))

(defvar coq-outline-heading-end-regexp "\.\\|\\*)")

(defvar coq-shell-outline-regexp coq-goal-regexp)
(defvar coq-shell-outline-heading-end-regexp coq-goal-regexp)

(defconst coq-kill-goal-command "Abort.")
(defconst coq-forget-id-command "Reset ")

(defconst coq-undoable-commands-regexp (proof-ids-to-regexp coq-tactics))

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
  (proof-shell-invisible-command (format "Set Undo %s." undos)))

;;
;; FIXME Papageno 05/1999: must take sections in account.
;;

(defun coq-count-undos (span)
  "Count number of undos in a span, return the command needed to undo that far."
  (let ((ct 0) str i)
    (if (and span (prev-span span 'type)
	     (not (eq (span-property (prev-span span 'type) 'type) 'comment))
	     (coq-goal-command-p
	      (span-property (prev-span span 'type) 'cmd)))
	(concat "Restart" proof-terminal-string)
      (while span
	(setq str (span-property span 'cmd))
	(cond ((eq (span-property span 'type) 'vanilla)
	       (if (proof-string-match coq-undoable-commands-regexp str)
		   (setq ct (+ 1 ct))))
	      ((eq (span-property span 'type) 'pbp)
	       (cond ((proof-string-match coq-undoable-commands-regexp str)
		      (setq i 0)
		      (while (< i (length str))
			(if (= (aref str i) proof-terminal-char)
			    (setq ct (+ 1 ct)))
			(setq i (+ 1 i))))
		     (t nil))))
	(setq span (next-span span 'type)))
      (concat "Undo " (int-to-string ct) proof-terminal-string))))

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
       (not (proof-string-match "Definition.*:=" str))))

;; TODO : add the stuff to handle the "Correctness" command

(defun coq-find-and-forget (span)
  (let (str ans)
    (while (and span (not ans))
      (setq str (span-property span 'cmd))
      (cond

       ((eq (span-property span 'type) 'comment))       

       ((eq (span-property span 'type) 'goalsave)
	;; Note da 6.10.99: in Lego and Isabelle, it's trivial to
	;; forget an unnamed theorem.  Coq really does use the 
	;; identifier "Unnamed_thm", though!  So we don't need
	;; this test:
	;; (unless (eq (span-property span 'name) proof-unnamed-theorem-name)
	(setq ans (concat coq-forget-id-command
			  (span-property span 'name) proof-terminal-string)))

       ((proof-string-match (concat "\\`\\(" coq-keywords-decl-defn-regexp
				    "\\)\\s-*\\(" proof-id 
				    ;; da: PG 3.1: I added "." here to try
				    ;; to get undo for Section working.
				    ;; (also changes in coq-syntax)
				    ;; Coq users will have to tell me if it
				    ;; works better now or not?
				    ;; At least I can do C-c C-r in files
				    ;; with Section in them.  But problem
				    ;; with closure still present:
				    ;; Section .. End Section should be
				    ;; atomic!
				    "\\)\\s-*[\\[,:.]") str)
	(setq ans (concat coq-forget-id-command
			  (match-string 2 str) proof-terminal-string)))

       ;; If it's not a goal but it contains "Definition" then it's a
       ;; declaration
       ((and (not (coq-goal-command-p str))
	     (proof-string-match
	      (concat "Definition\\s-+\\(" proof-id "\\)\\s-*:") str))
	(setq ans (concat coq-forget-id-command
			  (match-string 2 str) proof-terminal-string))))

      (setq span (next-span span 'type)))

      (or ans proof-no-command)))

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

;;
;; This code is broken
;; 
; (defun coq-lift-global (glob-span)
;   "This function lifts local lemmas from inside goals out to top level."
;   (let (start (next (span-at 1 'type)) str (goal-p nil))
;     (while (and next (and (not (eq next glob-span)) (not goal-p)))
;       (if (and (eq (span-property next 'type) 'vanilla)
; 	       (funcall proof-goal-command-p (span-property next 'cmd)))
; 	  (setq goal-p t)
; 	(setq next (next-span next 'type))))
    
;     (if (and next (not (eq next glob-span)))
; 	(progn
; 	  (proof-unlock-locked)
; 	  (setq str (buffer-substring (span-start glob-span)
; 				      (span-end glob-span)))
; 	  (delete-region (span-start glob-span) (span-end glob-span))
; 	  (goto-char (span-start next))
; 	  (setq start (point))
; 	  (insert str "\n")
; 	  (set-span-endpoints glob-span start (point))
; 	  (set-span-start next (point))
; 	  (proof-lock-unlocked)))))

(defun coq-state-preserving-p (cmd)
  (not (proof-string-match coq-undoable-commands-regexp cmd)))

(defun coq-global-p (cmd)
  (or (proof-string-match coq-keywords-decl-defn-regexp cmd)
      (and (proof-string-match
	    (concat "Definition\\s-+\\(" coq-id "\\)\\s-*:") cmd)
	   (proof-string-match ":=" cmd))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to coq                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-SearchIsos ()
  "Search a term whose type is isomorphic to given type
This is specific to coq-mode."
  (interactive)
  (let (cmd)
    (proof-shell-ready-prover) 
    (setq cmd (read-string "SearchIsos: " nil 'proof-minibuffer-history))
    (proof-shell-invisible-command
     (concat "SearchIsos " cmd proof-terminal-string))))

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
	       (buffer-string
		(progn (beginning-of-line) (forward-word 1) (point)) 
		(progn (end-of-line) (point)))))))
      (insert (concat "End" section)))))

(defun coq-Compile ()
  "compiles current buffer"
  (interactive)
  (let* ((n (buffer-name))
	 (l (string-match ".v" n)))
    (compile (concat "make " (substring n 0 l) ".vo"))))

(proof-defshortcut coq-Intros        "Intros "  [?i])
(proof-defshortcut coq-Apply         "Apply "   [?a])
(proof-defshortcut coq-begin-Section "Section " [?s])

(define-key coq-keymap [?e] 'coq-end-Section)
(define-key coq-keymap [?m] 'coq-Compile)
(define-key coq-keymap [?o] 'coq-SearchIsos)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Indentation                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "Case" is represented by 'c' on the stack, and
;; "CoInductive" is represented by 'C'.
(defun coq-stack-to-indent (stack)
  (cond
   ((null stack) 0)
   ((null (car (car stack)))
    (nth 1 (car stack)))
   (t (let ((col (save-excursion
		   (goto-char (nth 1 (car stack)))
		   (current-column))))
	(cond
	 ((eq (car (car stack)) ?c)
	  (save-excursion (move-to-column (current-indentation))
			  (cond 
			   ((eq (char-after (point)) ?|) (+ col 3))
			   ((proof-looking-at "end") col)
			   (t (+ col 5)))))	  
	 ((or (eq (car (car stack)) ?I) (eq (car (car stack)) ?C))
	  (+ col (if (eq ?| (save-excursion 
			      (move-to-column (current-indentation))
			      (char-after (point)))) 2 4)))
	 (t (1+ col)))))))

(defun coq-parse-indent (c stack)
  (cond
   ((eq c ?C)
    (cond ((proof-looking-at "Case")
	   (cons (list ?c (point)) stack))
	  ((proof-looking-at "CoInductive")
	   (forward-char (length "CoInductive"))
	   (cons (list c (- (point) (length "CoInductive"))) stack))
	  (t stack)))
   ((and (eq c ?e) (proof-looking-at "end") (eq (car (car stack)) ?c))
    (cdr stack))

   ((and (eq c ?I) (proof-looking-at "Inductive"))
    (forward-char (length "Inductive"))
    (cons (list c (- (point) (length "Inductive"))) stack))

   ((and (eq c ?.) (or (eq (car (car stack)) ?I) (eq (car (car stack)) ?C)))
    (cdr stack))

   (t stack)))

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
  (setq proof-comment-start "(*")
  (setq proof-comment-end "*)")
  (setq proof-unnamed-theorem-name "Unnamed_thm") ; Coq's default name

  (setq proof-assistant-home-page coq-www-home-page)

  (setq proof-mode-for-script 'coq-mode)

  (setq proof-guess-command-line 'coq-guess-command-line)

  ;; Commands sent to proof engine
  (setq proof-showproof-command "Show"
	proof-context-command "Print All"
	proof-goal-command "Goal %s."
	proof-save-command "Save %s."
	proof-find-theorems-command "Search %s."
;; FIXME da: Does Coq have a help or about command?
;;	proof-info-command "Help"
	proof-kill-goal-command coq-kill-goal-command)

  (setq proof-goal-command-p 'coq-goal-command-p
	proof-count-undos-fn 'coq-count-undos
	proof-find-and-forget-fn 'coq-find-and-forget
        proof-goal-hyp-fn 'coq-goal-hyp
	proof-state-preserving-p 'coq-state-preserving-p
	proof-global-p 'coq-global-p
	proof-parse-indent 'coq-parse-indent
	proof-stack-to-indent 'coq-stack-to-indent)

  (setq proof-save-command-regexp coq-save-command-regexp
	proof-save-with-hole-regexp coq-save-with-hole-regexp
	proof-goal-with-hole-regexp coq-goal-with-hole-regexp
	proof-indent-commands-regexp (proof-ids-to-regexp coq-keywords))

  (setq proof-auto-multiple-files t)	; until Coq has real support

  (setq proof-shell-start-silent-cmd "Begin Silent."
	proof-shell-stop-silent-cmd  "End Silent.")

  (coq-init-syntax-table)

;; font-lock

  (setq font-lock-keywords coq-font-lock-keywords-1)

  (setq proof-font-lock-zap-commas t)	; enable the painful hack
  
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
   proof-shell-first-special-char ?\360
   proof-shell-wakeup-char ?\371 ; done: prompt
   ;; The next three represent path annotation information
   proof-shell-start-char ?\372 ; not done
   proof-shell-end-char ?\373 ; not done
   proof-shell-field-char ?\374 ; not done
   proof-shell-goal-char ?\375 ; done
   proof-shell-eager-annotation-start "\376" ; done
   proof-shell-eager-annotation-start-length 1
   proof-shell-eager-annotation-end "\377" ; done
   proof-shell-annotated-prompt-regexp
   (concat proof-shell-prompt-pattern
	   (char-to-string proof-shell-wakeup-char)) ; done
   proof-shell-result-start "\372 Pbp result \373"
   proof-shell-result-end "\372 End Pbp result \373"
   proof-shell-start-goals-regexp "[0-9]+ subgoals?"
   proof-shell-end-goals-regexp proof-shell-annotated-prompt-regexp
   proof-shell-init-cmd coq-shell-init-cmd
   proof-shell-restart-cmd coq-shell-restart-cmd
   proof-analyse-using-stack t
   ;;	proof-lift-global 'coq-lift-global
   )
  
  (coq-init-syntax-table)
  (setq font-lock-keywords coq-font-lock-keywords-1)

  (proof-shell-config-done))

(defun coq-goals-mode-config ()
  (setq pbp-change-goal "Show %s.")
  (setq pbp-error-regexp coq-error-regexp)
  (coq-init-syntax-table)
  (setq font-lock-keywords coq-font-lock-keywords-1)
  (proof-goals-config-done))

(defun coq-response-config ()
   (coq-init-syntax-table)
   (setq font-lock-keywords coq-font-lock-keywords-1)
   (proof-response-config-done))

(provide 'coq)
