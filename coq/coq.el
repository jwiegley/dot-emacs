;; coq.el Major mode for Coq proof assistant
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Author: Healfdene Goguen and Thomas Kleymann
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;; Please let us know if you could maintain this package!

;; $Id$

(require 'proof-script)
(require 'coq-syntax)

;; Spans are our abstraction of extents/overlays.
(eval-and-compile
  (cond ((fboundp 'make-extent) (require 'span-extent))
	((fboundp 'make-overlay) (require 'span-overlay))))

(eval-and-compile
  (mapcar (lambda (f) (autoload f "proof-shell"))
	    '(pbp-mode proof-shell-config-done))) 
;; FIXME: outline and info should be autoloaded.
(require 'outline)
(require 'info)

; Configuration

(setq tags-always-exact t) ; Tags is unusable with Coq library otherwise:

(defcustom coq-tags "/usr/local/lib/coq/theories/TAGS"
  "the default TAGS table for the Coq library"
  :type 'string
  :group 'coq)

(defconst coq-process-config nil
  "Command to configure pretty printing of the Coq process for emacs.")

(defconst coq-interrupt-regexp "Interrupted"
  "Regexp corresponding to an interrupt")

(defcustom coq-default-undo-limit 100
  "Maximum number of Undo's possible when doing a proof."
  :type 'number
  :group 'coq)

;; ----- web documentation

(defcustom coq-www-home-page "http://pauillac.inria.fr/coq/"
  "Coq home page URL."
  :type 'string
  :group 'coq)

;; ----- coq-shell configuration options

(defcustom coq-prog-name "coqtop -emacs"
  "*Name of program to run as Coq."
  :type 'string
  :group 'coq)

(defvar coq-shell-prompt-pattern (concat "^" proof-id " < ")
  "*The prompt pattern for the inferior shell running coq.")

(defvar coq-shell-cd nil ; "Cd \"%s\"."
  "*Command of the inferior process to change the directory.") 

(defvar coq-shell-abort-goal-regexp "Current goal aborted"
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(defvar coq-shell-proof-completed-regexp "Subtree proved!"
  "*Regular expression indicating that the proof has been completed.")

(defvar coq-goal-regexp
  "\\(============================\\)\\|\\(subgoal [0-9]+ is:\\)\n")

;; ----- outline

(defvar coq-outline-regexp
  (proof-ids-to-regexp 
	   '("Section" "Chapter" "Goal" "Lemma" "Theorem" "Fact"
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

(define-derived-mode coq-shell-mode proof-shell-mode
   "coq-shell" 
   ;; With nil argument for docstring, Emacs makes up a nice one.
   nil
   (coq-shell-mode-config))

(define-derived-mode coq-mode proof-mode
   "coq" nil
   (coq-mode-config))

(define-derived-mode coq-pbp-mode pbp-mode
  "pbp" nil
  (coq-pbp-mode-config))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's coq specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; FIXME da: can't this be done by proof-shell-init-cmd ?
(defun coq-shell-init-hook ()
  (insert (format "Set Undo %s." coq-default-undo-limit))
  (insert (format "Cd \"%s\"." default-directory))
  (remove-hook 'proof-shell-insert-hook 'coq-shell-init-hook))

(defun coq-set-undo-limit (undos)
  (proof-shell-invisible-command (format "Set Undo %s." undos)))

(defun coq-count-undos (span)
  (let ((ct 0) str i)
    (if (and span (prev-span span 'type)
	     (not (eq (span-property (prev-span span 'type) 'type) 'comment))
	     (coq-goal-command-p
	      (span-property (prev-span span 'type) 'cmd)))
	(concat "Restart" proof-terminal-string)
      (while span
	(setq str (span-property span 'cmd))
	(cond ((eq (span-property span 'type) 'vanilla)
	       (if (string-match coq-undoable-commands-regexp str)
		   (setq ct (+ 1 ct))))
	      ((eq (span-property span 'type) 'pbp)
	       (cond ((string-match coq-undoable-commands-regexp str)
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
;; should have proof-goal-regexp instead.
(defun coq-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (and (string-match coq-goal-command-regexp str)
       (not (string-match "Definition.*:=" str))))

(defun coq-find-and-forget (span)
  (let (str ans)
    (while (and span (not ans))
      (setq str (span-property span 'cmd))
      (cond

       ((eq (span-property span 'type) 'comment))       

       ((eq (span-property span 'type) 'goalsave)
	(setq ans (concat coq-forget-id-command
			  (span-property span 'name) proof-terminal-string)))

       ((string-match (concat "\\`\\(" coq-keywords-decl-defn-regexp
                              "\\)\\s-*\\(" proof-id "\\)\\s-*[\\[,:]") str)
	(setq ans (concat coq-forget-id-command
			  (match-string 2 str) proof-terminal-string)))

       ;; If it's not a goal but it contains "Definition" then it's a
       ;; declaration
       ((and (not (coq-goal-command-p str))
	     (string-match
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

(defun coq-lift-global (glob-span)
  "This function lifts local lemmas from inside goals out to top level."
  (let (start (next (span-at 1 'type)) str (goal-p nil))
    (while (and next (and (not (eq next glob-span)) (not goal-p)))
      (if (and (eq (span-property next 'type) 'vanilla)
	       (funcall proof-goal-command-p (span-property next 'cmd)))
	  (setq goal-p t)
	(setq next (next-span next 'type))))

    (if (and next (not (eq next glob-span)))
	(progn
	  (proof-unlock-locked)
	  (setq str (buffer-substring (span-start glob-span)
				      (span-end glob-span)))
	  (delete-region (span-start glob-span) (span-end glob-span))
	  (goto-char (span-start next))
	  (setq start (point))
	  (insert str "\n")
	  (set-span-endpoints glob-span start (point))
	  (set-span-start next (point))
	  (proof-lock-unlocked)))))

(defun coq-state-preserving-p (cmd)
  (not (string-match coq-undoable-commands-regexp cmd)))

(defun coq-global-p (cmd)
  (or (string-match coq-keywords-decl-defn-regexp cmd)
      (and (string-match
	    (concat "Definition\\s-+\\(" coq-id "\\)\\s-*:") cmd)
	   (string-match ":=" cmd))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to coq                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-Intros () 
  "List proof state." 
  (interactive) 
  (insert "Intros "))

(defun coq-Apply () 
  "List proof state."  
  (interactive) 
  (insert "Apply "))

(defun coq-Search ()
  "Search for type in goals."
  (interactive)
  (let (cmd)
    (proof-shell-ready-prover) ;; was (proof-check-process-available)
    (setq cmd (read-string "Search Type: " nil 'proof-minibuffer-history))
    (proof-shell-invisible-command
     (concat "Search " cmd proof-terminal-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Indentation                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "Case" is represented by 'c' on the stack, and
;; "CoInductive is represented by 'C'.
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
			   ((looking-at "end") col)
			   (t (+ col 5)))))	  
	 ((or (eq (car (car stack)) ?I) (eq (car (car stack)) ?C))
	  (+ col (if (eq ?| (save-excursion 
			      (move-to-column (current-indentation))
			      (char-after (point)))) 2 4)))
	 (t (1+ col)))))))

(defun coq-parse-indent (c stack)
  (cond
   ((eq c ?C)
    (cond ((looking-at "Case")
	   (cons (list ?c (point)) stack))
	  ((looking-at "CoInductive")
	   (forward-char (length "CoInductive"))
	   (cons (list c (- (point) (length "CoInductive"))) stack))
	  (t stack)))
   ((and (eq c ?e) (looking-at "end") (eq (car (car stack)) ?c))
    (cdr stack))

   ((and (eq c ?I) (looking-at "Inductive"))
    (forward-char (length "Inductive"))
    (cons (list c (- (point) (length "Inductive"))) stack))

   ((and (eq c ?.) (or (eq (car (car stack)) ?I) (eq (car (car stack)) ?C)))
    (cdr stack))

   (t stack)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Coq shell startup and exit hooks                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-pre-shell-start ()
  (setq proof-prog-name coq-prog-name)
  (setq proof-mode-for-shell 'coq-shell-mode)
  (setq proof-mode-for-pbp 'coq-pbp-mode)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."

  (modify-syntax-entry ?\$ ".")
  (modify-syntax-entry ?\/ ".")
  (modify-syntax-entry ?\\ ".")
  (modify-syntax-entry ?+  ".")
  (modify-syntax-entry ?-  ".")
  (modify-syntax-entry ?=  ".")
  (modify-syntax-entry ?%  ".")
  (modify-syntax-entry ?<  ".")
  (modify-syntax-entry ?>  ".")
  (modify-syntax-entry ?\& ".")
  (modify-syntax-entry ?_  "_")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))

(defun coq-mode-config ()

  (setq proof-terminal-char ?\.)
  (setq proof-comment-start "(*")
  (setq proof-comment-end "*)")

  (setq proof-assistant-home-page coq-www-home-page)

  (setq proof-mode-for-script 'coq-mode)

  (setq proof-prf-string "Show"
	proof-ctxt-string "Print All"
	proof-help-string "Help")

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
	proof-kill-goal-command coq-kill-goal-command
	proof-commands-regexp (proof-ids-to-regexp coq-keywords))

  (coq-init-syntax-table)

;; font-lock

  (setq font-lock-keywords coq-font-lock-keywords-1)

  (proof-config-done)

  (define-key (current-local-map) [(control c) ?I] 'coq-Intros)
  (define-key (current-local-map) [(control c) ?a] 'coq-Apply)
  (define-key (current-local-map) [(control c) (control s)] 'coq-Search)

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
  (setq proof-shell-prompt-pattern coq-shell-prompt-pattern
        proof-shell-cd coq-shell-cd
        proof-shell-abort-goal-regexp coq-shell-abort-goal-regexp
        proof-shell-proof-completed-regexp coq-shell-proof-completed-regexp
        proof-shell-error-regexp coq-error-regexp
	proof-shell-interrupt-regexp coq-interrupt-regexp
        proof-shell-assumption-regexp coq-id
        proof-shell-goal-regexp coq-goal-regexp
        proof-shell-first-special-char ?\360
        proof-shell-wakeup-char ?\371 ; done: prompt
        ; The next three represent path annotation information
	proof-shell-start-char ?\372 ; not done
        proof-shell-end-char ?\373 ; not done
        proof-shell-field-char ?\374 ; not done
        proof-shell-goal-char ?\375 ; done
	proof-shell-eager-annotation-start "\376" ; done
	proof-shell-eager-annotation-end "\377" ; done
        proof-shell-annotated-prompt-regexp
	(concat proof-shell-prompt-pattern
		(char-to-string proof-shell-wakeup-char)) ; done
        proof-shell-result-start "\372 Pbp result \373"
        proof-shell-result-end "\372 End Pbp result \373"
        proof-shell-start-goals-regexp "[0-9]+ subgoals?"
        proof-shell-end-goals-regexp proof-shell-annotated-prompt-regexp
        proof-shell-init-cmd nil
	proof-analyse-using-stack t
	proof-lift-global 'coq-lift-global)

  ;; The following hook is removed once it's called.
  (add-hook 'proof-shell-insert-hook 'coq-shell-init-hook nil t)

  (coq-init-syntax-table)

  (proof-shell-config-done))

(defun coq-pbp-mode-config ()
  (setq pbp-change-goal "Show %s.")
  (setq pbp-error-regexp coq-error-regexp))

(provide 'coq)
