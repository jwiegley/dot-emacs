;; isa.el Major mode for Isabelle proof assistant
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;; Author: David Aspinall
;;
;; $Id$
;;


(require 'isa-syntax)
(require 'outline)
(require 'proof)


;;;
;;; ======== User settings for Isabelle ========
;;;

(defgroup isabelle-settings nil
  "Customization of Isabelle specifics for proof mode."
  :group 'proof)
  
(defcustom isa-prog-name "/usr/lib/Isabelle98/bin/isabelle"
  "*Name of program to run Isabelle."
  :type 'file
  :group 'isabelle-settings)

(defcustom isa-thy-file-tags-table "/usr/lib/Isabelle98/src/TAGS.thy"
  "*Name of theory file tags table for Isabelle."
  :type 'file
  :group 'isabelle-settings)

(defcustom isa-ML-file-tags-table  "/usr/lib/Isabelle98/src/TAGS.ML"
  "*Name of ML file tags table for Isabelle."
  :type 'file
  :group 'isabelle-settings)

(defcustom isa-indent 2
  "*Indentation degree in proof scripts.
Utterly irrelevant for Isabelle because normal proof scripts have
no regular or easily discernable structure."
  :type 'number
  :group 'isabelle-settings)

(defcustom isa-www-home-page
  ;; "http://www.cl.cam.ac.uk/Research/HVG/isabelle.html"
  "http://www.dcs.ed.ac.uk/home/isabelle"
  "URL of home page for Isabelle."
  :type 'string
  :group 'isabelle-settings)
  
  
  

;;;
;;; ======== Configuration of generic modes ========
;;;

(defun isa-mode-config-set-variables
  "Configure generic proof scripting mode variables for Isabelle."
  (setq
   proof-assistant		"Isabelle"
   proof-www-home-page	isa-www-home-page
   ;; proof script syntax
   proof-terminal-char	?\;	; ends a proof
   proof-comment-start	"(*"	; comment in a proof
   proof-comment-end		"*)"	; 
   ;; proof engine output syntax
   proof-save-command-regexp   isa-save-command-regexp
   proof-save-with-hole-regexp isa-save-with-hole-regexp
   proof-goal-with-hole-regexp isa-goal-with-hole-regexp
   proof-kill-goal-command	 ""   ; FIXME: proof.el should allow nil
   proof-commands-regexp	 (ids-to-regexp isa-keywords)
   ;; proof engine commands
   proof-prf-string		"pr()"
   proof-ctxt-string		"the_context();"
   proof-help-string ; could be version 
   "print \" in-built help for Isabelle.\"" ; FIXME: proof.el should allow nil
   ;; command hooks
   proof-goal-command-p	'isa-goal-command-p
   proof-count-undos-fn	'isa-count-undos
   proof-find-and-forget-fn	'isa-find-and-forget
   proof-goal-hyp-fn		'isa-goal-hyp
   proof-state-preserving-p	'isa-state-preserving-p
   proof-global-p		'isa-global-p    ; FIXME: proof.el should allow nil
   proof-parse-indent		'isa-parse-indent
   proof-stack-to-indent	'isa-stack-to-indent))


(defun isa-shell-mode-config-set-variables
  "Configure generic proof shell mode variables for Isabelle."
  (setq
   proof-shell-prompt-pattern		"^2?[---=#>]>? *\\|^\\*\\* .*" ; for ML
   proof-shell-cd			"cd \"%s\";"
   ;; this one not set: proof-shell-abort-goal-regexp 
   proof-shell-proof-completed-regexp   "No subgoals!"
   proof-shell-error-regexp		isa-error-regexp
   proof-shell-interrupt-regexp         "Interrupt"     ; FIXME: only good for NJ/SML
   proof-shell-noise-regexp	        ""
   proof-shell-assumption-regexp	isa-id		   ; matches name of assumptions
   proof-shell-goal-regexp		isa-goal-regexp    ; matches subgoal heading
   ;; We can't hack the SML prompt, so set wakeup-char to nil.
   proof-shell-wakeup-char		nil
   proof-shell-start-goals-regexp	"\370"
   proof-shell-end-goals-regexp		"\371"
   ;; initial command configures Isabelle by hacking print functions.
   ;; may need to set directory somewhere for this:
   ;; /home/da/devel/lego/elisp/   or  $PROOFGENERIC_HOME ?
   proof-shell-init-cmd			"use \"isa-print-functions.ML\";"
   ;; === ANNOTATIONS  === remaining ones broken
   proof-shell-goal-char	        ?\375
   proof-shell-first-special-char	?\360
   proof-shell-eager-annotation-start "\376" 
   proof-shell-eager-annotation-end   "\377"
   proof-shell-annotated-prompt-regexp proof-shell-prompt-pattern ; can't annotate!
   proof-shell-result-start	        "\372 Pbp result \373"
   proof-shell-result-end		"\372 End Pbp result \373"
   proof-analyse-using-stack		t
   proof-shell-start-char		?\372
   proof-shell-end-char			?\373
   proof-shell-field-char		?\374))


;; ===== outline mode

;;; FIXME: test and add more things here
(defvar isa-outline-regexp
  (ids-to-regexp '("goal" "Goal" "prove_goal"))
  "Outline regexp for Isabelle ML files")

;;; End of a command needs parsing to find, so this is approximate.
(defvar isa-outline-heading-end-regexp ";[ \t\n]*")

(defconst isa-goal-regexp "^[ \t]*[0-9]+\\. "
  "Regexp to match subgoal headings.
Used by proof mode to parse proofstate output, and also
to set outline heading regexp.")
  
;; 
(defvar isa-shell-outline-regexp isa-goal-regexp)
(defvar isa-shell-outline-heading-end-regexp isa-goal-regexp)

;;; ---- end-outline


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;  FIXME: I don't think they should be here at all.

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


;; FIXME: think about the next variable.  I've changed sense from
;;  LEGO and Coq's treatment.
(defconst isa-not-undoable-commands-regexp
  (ids-to-regexp '("undo" "back"))
  "Regular expression matching commands which are *not* undoable.")

;; This next function is the important one for undo operations.
(defun isa-count-undos (span)
  "Count number of undos in a span, return the command needed to undo that far."
  (let ((ct 0) str i)
    (if (and span (prev-span span 'type)
	     (not (eq (span-property (prev-span span 'type) 'type) 'comment))
	     (isa-goal-command-p
	      (span-property (prev-span span 'type) 'cmd)))
	(concat "choplev 0" proof-terminal-string)
      (while span
	(setq str (span-property span 'cmd))
	(cond ((eq (span-property span 'type) 'vanilla)
	       (or (string-match isa-not-undoable-commands-regexp str)
		   (setq ct (+ 1 ct))))
	      ((eq (span-property span 'type) 'pbp)
	       ;; this case probably redundant for Isabelle, unless
	       ;; we think of some nice ways of matching non-undoable
	       ;; commands.
	       (cond ((not (string-match isa-not-undoable-commands-regexp str))
		      (setq i 0)
		      (while (< i (length str))
			(if (= (aref str i) proof-terminal-char)
			    (setq ct (+ 1 ct)))
			(setq i (+ 1 i))))
		     (t nil))))
	(setq span (next-span span 'type)))
      (concat "choplev " (int-to-string ct) proof-terminal-string))))

(defun isa-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (string-match isa-goal-command-regexp str)) ; this regexp defined in isa-syntax.el

;; Isabelle has no concept of a Linear context, so forgetting back
;; to the declaration of a particular something makes no real
;; sense.  Perhaps in the future there will be functions to remove
;; theorems from theories, but even then all we could do is
;; forget particular theorems one by one.  So we ought to search
;; backwards in isa-find-and-forget, rather than forwards as
;; the old code below does.

(defun isa-find-and-forget (span)
  ;; Special return value to indicate nothing needs to be done.
  "COMMENT")
  
  
;; BEGIN Old code  (taken from Coq.el)
;(defconst isa-keywords-decl-defn-regexp
;  (ids-to-regexp (append isa-keywords-decl isa-keywords-defn))
;  "Declaration and definition regexp.")
;(defun isa-find-and-forget (span)
;  (let (str ans)
;    (while (and span (not ans))
;      (setq str (span-property span 'cmd))
;      (cond
;       ((eq (span-property span 'type) 'comment))       

;       ((eq (span-property span 'type) 'goalsave)
;	(setq ans (concat isa-forget-id-command
;			  (span-property span 'name) proof-terminal-string)))

;       ((string-match (concat "\\`\\(" isa-keywords-decl-defn-regexp
;                              "\\)\\s-*\\(" proof-id "\\)\\s-*[\\[,:]") str)
;	(setq ans (concat isa-forget-id-command
;			  (match-string 2 str) proof-terminal-string)))
;       ;; If it's not a goal but it contains "Definition" then it's a
;       ;; declaration
;       ((and (not (isa-goal-command-p str))
;	     (string-match
;	      (concat "Definition\\s-+\\(" proof-id "\\)\\s-*:") str))
;	(setq ans (concat isa-forget-id-command
;			  (match-string 2 str) proof-terminal-string))))
;      (setq span (next-span span 'type)))
;      (or ans "COMMENT")))
; END old code 

(defvar isa-current-goal 1
  "Last goal that emacs looked at.")

;; Parse proofstate output.  Isabelle does not display
;; named hypotheses in the proofstate output:  they
;; appear as a list in each subgoal.  Ignore
;; that aspect for now and just return the
;; subgoal number.
(defun isa-goal-hyp ()
  (if (looking-at proof-shell-goal-regexp)
      (cons 'goal (match-string 1))))

(defun isa-state-preserving-p (cmd)
  "Non-nil if command preserves the proofstate."
  (string-match isa-not-undoable-commands-regexp cmd))

;; FIXME: I don't really know what this means, but lego sets
;; it to always return nil.  Probably should be able to
;; leave it unset.
(defun isa-global-p (cmd)
  nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Indentation                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; Sadly this is pretty pointless for Isabelle.
;; Proof scripts in Isabelle don't really have an easily-observed
;; block structure  -- a case split can be done by any obscure tactic,
;; and then solved in a number of steps that bears no relation to the
;; number of cases!  And the end is certainly not marked in anyway.
;; 
(defun isa-stack-to-indent (stack)
    (cond
   ((null stack) 0)
   ((null (car (car stack)))
    (nth 1 (car stack)))
   (t (save-excursion
	(goto-char (nth 1 (car stack)))
	(+ isa-indent (current-column))))))

(defun isa-parse-indent (c stack)
  "Indentation function for Isabelle.  Does nothing."
  stack)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Isa shell startup and exit hooks                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isa-pre-shell-start ()
  (setq proof-prog-name		isa-prog-name)
  (setq proof-mode-for-shell    'isa-shell-mode)
  (setq proof-mode-for-pbp	'isa-pbp-mode))

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
  (isa-mode-config-set-variables)
  (isa-init-syntax-table)
  ;; font-lock
  (setq font-lock-keywords isa-font-lock-keywords-1)
  (proof-config-done)
  (define-key (current-local-map) [(control c) ?I] 'isa-Intros)
  (define-key (current-local-map) [(control c) ?a] 'isa-Apply)
  (define-key (current-local-map) [(control c) (control s)] 'isa-Search)
  ;; outline
  ;; FIXME: do we need to call make-local-variable here?
  (make-local-variable 'outline-regexp)
  (setq outline-regexp isa-outline-regexp)
  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp isa-outline-heading-end-regexp)
  ;; tags
  ;  (and (boundp 'tag-table-alist)
  ;       (setq tag-table-alist
  ;	     (append '(("\\.ML$"  . isa-ML-file-tags-table)
  ;		       ("\\.thy$" . isa-thy-file-tags-table))
  ;		     tag-table-alist)))
  (setq blink-matching-paren-dont-ignore-comments t)
  ;; hooks and callbacks
  (add-hook 'proof-pre-shell-start-hook 'isa-pre-shell-start nil t))


(defun isa-shell-mode-config ()
  ;; The following hook is removed once it's called.
  ;; FIXME: maybe add this back later.
  ;;(add-hook 'proof-shell-insert-hook 'isa-shell-init-hook nil t)
  (isa-init-syntax-table)
  (isa-shell-mode-config-set-variables)
  (proof-shell-config-done))

;; FIXME: broken, of course, as is all PBP everywhere.
(defun isa-pbp-mode-config ()
  (setq pbp-change-goal "Show %s.")
  (setq pbp-error-regexp isa-error-regexp))

(provide 'isa)
