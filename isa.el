;; isa.el Major mode for Isabelle proof assistant
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;; Authors: Healfdene Goguen, Thomas Kleymann, David Aspinall

;; $Log$
;; Revision 1.1  1998/08/11 14:43:34  da
;; Isabelle proof.el support.
;;


(require 'isa-syntax)
(require 'outline)
(require 'proof)

; Configuration

(defvar isa-assistant "Isabelle"
  "Name of proof assistant")

(defvar isa-tags nil ; "/usr/local/lib/isa/theories/TAGS"
  "the default TAGS table for the Isa library")

(defconst isa-process-config nil
  "Command to configure pretty printing of the Isa process for emacs.")

(defconst isa-interrupt-regexp "Interrupt"
  "Regexp corresponding to an interrupt")

(defvar isa-save-query t
  "*If non-nil, ask user for permission to save the current buffer before
  processing a module.")

(defvar isa-default-undo-limit 100
  "Maximum number of Undo's possible when doing a proof.")

;; ----- web documentation

(defvar isa-www-home-page "http://www.cl.cam.ac.uk/Research/HVG/isabelle.html")

;; ----- isa-shell configuration options

;; FIXME: needs to have special characters for proof.el, also path
;; name shouldn't be here.
(defvar isa-prog-name "/usr/lib/Isabelle98/bin/isabelle"
  "*Name of program to run as Isabelle.")

(defvar isa-shell-working-dir ""
  "The working directory of the isabelle shell")

(defvar isa-shell-prompt-pattern 
  "^2?[---=#>]>? *\\|^\\*\\* .*"
  "*The prompt pattern for the inferior shell running isabelle.")

(defvar isa-shell-cd "cd \"%s\";"
  "*Command of the inferior process to change the directory.") 

;; FIXME: check this?
; Don't define this, no correspondence.
;(defvar isa-shell-abort-goal-regexp nil 
;  "*Regular expression indicating that the proof of the current goal
;  has been abandoned.")

(defvar isa-shell-proof-completed-regexp "No subgoals!"
  "*Regular expression indicating that the proof has been completed.")

(defvar isa-goal-regexp
  "^[ \t]*[0-9]+\\. "
  "Regexp to match subgoal heading.")

;; ----- outline

;;; FIXME: BROKEN
(defvar isa-outline-regexp
  (ids-to-regexp 
	   '("Section" "Chapter" "Goal" "Lemma" "Theorem" "Fact"
	   "Remark" "Record" "Inductive" "Definition")))

(defvar isa-outline-heading-end-regexp "\.\\|\\*)")

(defvar isa-shell-outline-regexp isa-goal-regexp)
(defvar isa-shell-outline-heading-end-regexp isa-goal-regexp)

;;; ---- end-outline

(defconst isa-kill-goal-command nil) ; "Abort."
(defconst isa-forget-id-command nil) ; "Reset "

;;; FIXME!!
(defconst isa-undoable-commands-regexp (ids-to-regexp isa-tactics))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-derived-mode isa-shell-mode proof-shell-mode
   "isa-shell" "Inferior shell mode for isabelle shell"
   (isa-shell-mode-config))

(define-derived-mode isa-mode proof-mode
   "isa" "Isabelle Mode"
   (isa-mode-config))

(define-derived-mode isa-pbp-mode pbp-mode
  "pbp" "Proof-by-pointing support for Isabelle"
  (isa-pbp-mode-config))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's Isabelle specific                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(defun isa-shell-init-hook ()
;  (remove-hook 'proof-shell-insert-hook 'isa-shell-init-hook))

;(defun isa-set-undo-limit (undos)
;  (proof-invisible-command (format "Set Undo %s." undos)))

(defun isa-count-undos (span)
  (let ((ct 0) str i)
    (if (and span (prev-span span 'type)
	     (not (eq (span-property (prev-span span 'type) 'type) 'comment))
	     (isa-goal-command-p
	      (span-property (prev-span span 'type) 'cmd)))
	(concat "Restart" proof-terminal-string)
      (while span
	(setq str (span-property span 'cmd))
	(cond ((eq (span-property span 'type) 'vanilla)
	       (if (string-match isa-undoable-commands-regexp str)
		   (setq ct (+ 1 ct))))
	      ((eq (span-property span 'type) 'pbp)
	       (cond ((string-match isa-undoable-commands-regexp str)
		      (setq i 0)
		      (while (< i (length str))
			(if (= (aref str i) proof-terminal-char)
			    (setq ct (+ 1 ct)))
			(setq i (+ 1 i))))
		     (t nil))))
	(setq span (next-span span 'type)))
      (concat "Undo " (int-to-string ct) proof-terminal-string))))

(defconst isa-keywords-decl-defn-regexp
  (ids-to-regexp (append isa-keywords-decl isa-keywords-defn))
  "Declaration and definition regexp.")

(defun isa-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (and (string-match isa-goal-command-regexp str)
       (not (string-match "Definition.*:=" str))))

(defun isa-find-and-forget (span)
  (let (str ans)
    (while (and span (not ans))
      (setq str (span-property span 'cmd))
      (cond

       ((eq (span-property span 'type) 'comment))       

       ((eq (span-property span 'type) 'goalsave)
	(setq ans (concat isa-forget-id-command
			  (span-property span 'name) proof-terminal-string)))

       ((string-match (concat "\\`\\(" isa-keywords-decl-defn-regexp
                              "\\)\\s-*\\(" proof-id "\\)\\s-*[\\[,:]") str)
	(setq ans (concat isa-forget-id-command
			  (match-string 2 str) proof-terminal-string)))

       ;; If it's not a goal but it contains "Definition" then it's a
       ;; declaration
       ((and (not (isa-goal-command-p str))
	     (string-match
	      (concat "Definition\\s-+\\(" proof-id "\\)\\s-*:") str))
	(setq ans (concat isa-forget-id-command
			  (match-string 2 str) proof-terminal-string))))

      (setq span (next-span span 'type)))

      (or ans "COMMENT")))

(defvar isa-current-goal 1
  "Last goal that emacs looked at.")

(defun isa-goal-hyp ()
  (cond 
   ((looking-at "============================\n")
    (goto-char (match-end 0))
    (cons 'goal (int-to-string isa-current-goal)))
   ((looking-at "subgoal \\([0-9]+\\) is:\n")
    (goto-char (match-end 0))
    (cons 'goal (match-string 1))
    (setq isa-current-goal (string-to-int (match-string 1))))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))

(defun isa-state-preserving-p (cmd)
  (not (string-match isa-undoable-commands-regexp cmd)))

(defun isa-global-p (cmd)
  (or (string-match isa-keywords-decl-defn-regexp cmd)
      (and (string-match
	    (concat "Definition\\s-+\\(" isa-id "\\)\\s-*:") cmd)
	   (string-match ":=" cmd))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to Isabelle                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isa-Intros () 
  "List proof state." 
  (interactive) 
  (insert "printlev"))

(defun isa-Apply () 
  "List proof state."  
  (interactive) 
  (insert "Apply "))

(defun isa-Search ()
  "Search for type in goals."
  (interactive)
  (let (cmd)
    (proof-check-process-available)
    (setq cmd (read-string "Search Type: " nil 'proof-minibuffer-history))
    (proof-invisible-command (concat "Search " cmd proof-terminal-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Indentation                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "Case" is represented by 'c' on the stack, and
;; "CoInductive is represented by 'C'.
(defun isa-stack-to-indent (stack)
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

(defun isa-parse-indent (c stack)
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
;;   Isa shell startup and exit hooks                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isa-pre-shell-start ()
  (setq proof-prog-name isa-prog-name)
  (setq proof-mode-for-shell 'isa-shell-mode)
  (setq proof-mode-for-pbp 'isa-pbp-mode)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isa-init-syntax-table ()
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

(defun isa-mode-config ()

  (setq proof-terminal-char ?\;)
  (setq proof-comment-start "(*")
  (setq proof-comment-end "*)")

  (setq proof-assistant isa-assistant
	proof-www-home-page isa-www-home-page)

  (setq proof-prf-string "Show"
	proof-ctxt-string "Print All"
	proof-help-string "Help")

  (setq proof-goal-command-p 'isa-goal-command-p
	proof-count-undos-fn 'isa-count-undos
	proof-find-and-forget-fn 'isa-find-and-forget
        proof-goal-hyp-fn 'isa-goal-hyp
	proof-state-preserving-p 'isa-state-preserving-p
	proof-global-p 'isa-global-p
	proof-parse-indent 'isa-parse-indent
	proof-stack-to-indent 'isa-stack-to-indent)

  (setq proof-save-command-regexp isa-save-command-regexp
	proof-save-with-hole-regexp isa-save-with-hole-regexp
	proof-goal-with-hole-regexp isa-goal-with-hole-regexp
	proof-kill-goal-command isa-kill-goal-command
	proof-commands-regexp (ids-to-regexp isa-keywords))

  (isa-init-syntax-table)

;; font-lock

  (setq font-lock-keywords isa-font-lock-keywords-1)

  (proof-config-done)

  (define-key (current-local-map) [(control c) ?I] 'isa-Intros)
  (define-key (current-local-map) [(control c) ?a] 'isa-Apply)
  (define-key (current-local-map) [(control c) (control s)] 'isa-Search)

;; outline
  
  (make-local-variable 'outline-regexp)
  (setq outline-regexp isa-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp isa-outline-heading-end-regexp)

;; tags
  (and (boundp 'tag-table-alist)
       (setq tag-table-alist
	     (append '(("\\.v$" . isa-tags)
		       ("isa"  . isa-tags))
		     tag-table-alist)))

  (setq blink-matching-paren-dont-ignore-comments t)

;; hooks and callbacks

  (add-hook 'proof-shell-exit-hook 'isa-zap-line-width nil t)
  (add-hook 'proof-pre-shell-start-hook 'isa-pre-shell-start nil t))

(defun isa-shell-mode-config ()
  (setq proof-shell-prompt-pattern isa-shell-prompt-pattern
        proof-shell-cd isa-shell-cd
; this one not set.
;        proof-shell-abort-goal-regexp isa-shell-abort-goal-regexp
        proof-shell-proof-completed-regexp isa-shell-proof-completed-regexp
        proof-shell-error-regexp isa-error-regexp
	proof-shell-interrupt-regexp isa-interrupt-regexp
        proof-shell-noise-regexp ""
        proof-shell-assumption-regexp isa-id
        proof-shell-goal-regexp isa-goal-regexp
        proof-shell-first-special-char ?\360
        proof-shell-wakeup-char ?> ; ?\371 ; done: prompt
        ; The next three represent path annotation information
	proof-shell-start-char nil ; ?\372 ; not done
        proof-shell-end-char nil ; ?\373 ; not done
        proof-shell-field-char nil ; ?\374 ; not done
        proof-shell-goal-char nil ; ?\375 ; done
	proof-shell-eager-annotation-start "\376" ; done
	proof-shell-eager-annotation-end "\377" ; done
        proof-shell-annotated-prompt-regexp proof-shell-prompt-pattern
	;(concat proof-shell-prompt-pattern
	;	(char-to-string proof-shell-wakeup-char)) ; done
        proof-shell-result-start "\372 Pbp result \373"
        proof-shell-result-end "\372 End Pbp result \373"
        proof-shell-start-goals-regexp "^Level" ; isa-goal-regexp ;  -9]+ subgoals?"
        proof-shell-end-goals-regexp proof-shell-annotated-prompt-regexp
        proof-shell-init-cmd nil
	proof-analyse-using-stack t)

  ;; The following hook is removed once it's called.
  ;; FIXME: maybe add this back later.
  ;;(add-hook 'proof-shell-insert-hook 'isa-shell-init-hook nil t)

  (isa-init-syntax-table)

  (proof-shell-config-done))

(defun isa-pbp-mode-config ()
  (setq pbp-change-goal "Show %s.")
  (setq pbp-error-regexp isa-error-regexp))

(provide 'isa)
