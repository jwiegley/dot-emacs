;; isa.el Major mode for Isabelle proof assistant
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Isabelle maintainer <isabelle@dcs.ed.ac.uk>

;;
;; $Id$
;;


(require 'isa-syntax)
(require 'outline)
(setq proof-tags-support nil)  ; we don't want it, no isatags prog.
(require 'proof)


;;;
;;; ======== User settings for Isabelle ========
;;;

(defcustom isabelle-prog-name "isabelle"
  "*Name of program to run Isabelle."
  :type 'file
  :group 'isabelle)

(defcustom isabelle-indent 2
  "*Indentation degree in proof scripts.
Somewhat irrelevant for Isabelle because normal proof scripts have
no regular or easily discernable structure."
  :type 'number
  :group 'isabelle)

(defcustom isabelle-web-page
  ;; "http://www.cl.cam.ac.uk/Research/HVG/isabelle.html"
  "http://www.dcs.ed.ac.uk/home/isabelle"
  "URL of web page for Isabelle."
  :type 'string
  :group 'isabelle)
  
  
  

;;;
;;; ======== Configuration of generic modes ========
;;;

;;; NB!  Disadvantage of *not* shadowing variables is that user
;;; cannot override them.  It might be nice to override some
;;; variables, which ones?

(defun isa-mode-config-set-variables ()
  "Configure generic proof scripting mode variables for Isabelle."
  (setq
   proof-www-home-page		isabelle-web-page
   ;; proof script syntax
   proof-terminal-char		?\;	; ends a proof
   proof-comment-start		"(*"	; comment in a proof
   proof-comment-end		"*)"	; 
   ;; proof engine output syntax
   proof-save-command-regexp    isa-save-command-regexp
   proof-save-with-hole-regexp  isa-save-with-hole-regexp
   proof-goal-with-hole-regexp  isa-goal-with-hole-regexp
   proof-commands-regexp	(ids-to-regexp isa-keywords)
   ;; proof engine commands (first three for menus, last for undo)
   proof-prf-string		"pr();"
   proof-goal-command		"Goal \"%s\";"
   proof-save-command		"qed \"%s\";"
   proof-ctxt-string		"ProofGeneral.show_context();"
   proof-help-string		"ProofGeneral.help();"
   proof-kill-goal-command	"ProofGeneral.kill_goal();"
   ;; command hooks
   proof-goal-command-p		'isa-goal-command-p
   proof-count-undos-fn		'isa-count-undos
   proof-find-and-forget-fn	'isa-find-and-forget
   proof-goal-hyp-fn		'isa-goal-hyp
   proof-state-preserving-p	'isa-state-preserving-p
   proof-parse-indent		'isa-parse-indent
   proof-stack-to-indent	'isa-stack-to-indent))


(defun isa-shell-mode-config-set-variables ()
  "Configure generic proof shell mode variables for Isabelle."
  (setq
   ;; This first pattern is crucial.
   ;; It should match the 'top-level' prompt from ML,
   ;; optionally proceeded by vacuous assignment output.
   ;;
   ;; It doesn't match the tracing output prompt or secondary
   ;; prompts (continued lines), although these would usually
   ;; be nice for comint-prompt-regexp to work.
   ;; 
   ;; Probably it isn't general enough for all MLs, please send me
   ;; problem reports / patches.
   ;;
   proof-shell-annotated-prompt-regexp
					"^\\(val it = () : unit\n\\)?> "

   ;; This pattern is just for comint, it matches a range of
   ;; prompts from a range of MLs.
   proof-shell-prompt-pattern		"^2?[-=#>]>? *"

   proof-shell-cd			"cd \"%s\";"
   proof-shell-proof-completed-regexp   "No subgoals!"
   ;; FIXME: the next two are probably only good for NJ/SML
   proof-shell-error-regexp		"^.*Error:\\|^\\*\\*\\*"
   proof-shell-interrupt-regexp         "Interrupt"
   ;; this one not set: proof-shell-abort-goal-regexp 
   proof-shell-noise-regexp	        ""
   proof-shell-assumption-regexp	isa-id  ; matches name of assumptions
   proof-shell-goal-regexp		isa-goal-regexp    ; matches subgoal heading
   ;; We can't hack the SML prompt, so set wakeup-char to nil.
   proof-shell-wakeup-char		nil
   proof-shell-start-goals-regexp	"\370"
   proof-shell-end-goals-regexp		"\371"
   ;; initial command configures Isabelle by hacking print functions.
   ;; may need to set directory somewhere for this:
   ;; /home/da/devel/lego/elisp/   or  $PROOFGENERIC_HOME ?
   proof-shell-init-cmd			(concat
					 "use \""
					 proof-internal-home-directory
					  "isa/ProofGeneral.ML\";")
   proof-shell-eager-annotation-start   "^\\[opening \\|^###\\|^Reading\\|^Proof General"
   proof-shell-eager-annotation-end     "$"
   ;; === ANNOTATIONS  === ones below here are broken
   proof-shell-goal-char	        ?\375
   proof-shell-first-special-char	?\360
   proof-shell-result-start	        "\372 Pbp result \373"
   proof-shell-result-end		"\372 End Pbp result \373"
   proof-analyse-using-stack		t
   proof-shell-start-char		?\372
   proof-shell-end-char			?\373
   proof-shell-field-char		?\374
   ;; NEW NEW for multiple files
   ;; === NEW NEW: multiple file stuff.  move elsewhere later.
   proof-shell-process-file 
   (cons
    ;; Theory loader output 
    "Reading \"\\(.*\\.ML\\)\""
    (lambda (str)
      (match-string 1 str)))
   ;; This is the output returned by a special command to
   ;; query Isabelle for outdated files.
   proof-shell-retract-files-regexp
   "Proof General, you can unlock the file \"\\(.*\\)\""
   proof-shell-compute-new-files-list 'isa-shell-compute-new-files-list
   ))

(defun isa-shell-compute-new-files-list (str)
  (assert (member (file-truename (match-string 1 str))
		  proof-included-files-list))
  (remove (file-truename (match-string 1 str)) 
	  proof-included-files-list))


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


;;
;;   Define the derived modes 
;;
(define-derived-mode isa-shell-mode proof-shell-mode
   "Isabelle shell" nil
   (isa-shell-mode-config))

(define-derived-mode isa-pbp-mode pbp-mode
  "Isabelle proofstate" nil
  (isa-pbp-mode-config))

(define-derived-mode isa-proofscript-mode proof-mode
   "Isabelle script" nil
   (isa-mode-config))

;; Automatically selecting theory mode or Proof General script mode.

(defun isa-mode ()
  "Mode for Isabelle buffers: either isa-proofscript-mode or thy-mode.
Files with extension .thy will be in thy-mode, otherwise we choose
isa-proofscript-mode."
  (interactive)
  (cond
   ((string-match ".thy" (buffer-file-name))
    (thy-mode))
   (t 
    (isa-proofscript-mode))))

;; Next portion taken from isa-load.el
;; isa-load.el,v 3.8 1998/09/01 

(defcustom isabelle-use-sml-mode
   (if (fboundp 'sml-mode) 'sml-mode)
  "*If non-nil, attempt to use sml-mode in ML section of theory files."
  :type 'boolean
  :group 'isabelle)

(defgroup thy nil
  "Customization of Isamode's theory editing mode"
  ;; :link '(info-link "(Isamode)Theory Files")
  :load 'thy-mode
  :group 'isabelle)

(autoload 'thy-mode "thy-mode" 
	  "Major mode for Isabelle theory files" t nil)


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

(defconst isa-retract-file-command "retract_file \"%s\";"
  "Command sent to Isabelle for forgetting")

(defun isa-find-and-forget (span)
  ;; See if we are going to part way through a completely processed
  ;; buffer.
  (if (eq (current-buffer) (car-safe proof-script-buffer-list))
      ;; Special return value to indicate nothing needs to be done.
      proof-no-command 
    (progn
      (save-excursion
	(goto-char (point-max))
	(skip-chars-backward "\\S-")
	(if (member (proof-unprocessed-begin) (list (point-min) (point)))
	    ;; 
	    (format isa-retract-file-command 
		    (file-name-sans-extension 
		     (file-name-nondirectory
		      (buffer-file-name))))
	  prog-no-command)))))


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
	(+ isabelle-indent (current-column))))))

(defun isa-parse-indent (c stack)
  "Indentation function for Isabelle.  Does nothing."
  stack)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Isa shell startup and exit hooks                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isa-pre-shell-start ()
  (setq proof-prog-name		isabelle-prog-name)
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
  (setq font-lock-keywords isa-font-lock-keywords-1)
  (proof-config-done)
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
  ;		       ("\\.thy$" . thy-file-tags-table))
  ;		     tag-table-alist)))
  (setq blink-matching-paren-dont-ignore-comments t)
  ;; hooks and callbacks
  (add-hook 'proof-pre-shell-start-hook 'isa-pre-shell-start nil t))

(defun isa-shell-mode-config ()
  "Configure Proof General proof shell for Isabelle."
  (isa-init-syntax-table)
  (isa-shell-mode-config-set-variables)
  (proof-shell-config-done))

;; FIXME: broken, of course, as is all PBP everywhere.
(defun isa-pbp-mode-config ()
  (setq pbp-change-goal "Show %s.")
  (setq pbp-error-regexp proof-shell-error-regexp))

(provide 'isa)
