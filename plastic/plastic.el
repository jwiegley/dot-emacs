;; plastic.el  - Major mode for Plastic proof assistant
;; Author: Paul Callaghan <P.C.Callaghan@durham.ac.uk>
;; Maintainer: <author>
;; $Id$

;; adapted from the following, by Paul Callaghan
;; ;; lego.el Major mode for LEGO proof assistants
;; ;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; ;; Author:      Thomas Kleymann and Dilip Sequeira
;; ;; Maintainer: Paul Callaghan <P.C.Callaghan@durham.ac.uk>
;; ;;
;; ;; lego.el,v 2.27 1998/11/25 12:56:47 da Exp

;; NOTES:
;;	remember to prefix all potential cmds with plastic-lit-string
;;	alternative is to fix the filtering 


(require 'proof)
;;FIXME: proof-script should be autoloaded
(require 'proof-script)

;;FIXME: proof-shell should be autoloaded
(require 'proof-shell)
(require 'plastic-syntax)

;; FIXME: outline should be autoloaded
(require 'outline)

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User Configuration ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I believe this is standard for Linux under RedHat -tms
(defcustom plastic-tags "TO BE DONE"
  "*The directory of the TAGS table for the Plastic library"
  :type 'file
  :group 'plastic)

(defcustom plastic-indent 2
  "*Indentation"
  :type 'number
  :group 'plastic)

(defcustom plastic-test-all-name "need_a_global_lib"
  "*The name of the LEGO module which inherits all other modules of the
  library."
  :type 'string
  :group 'plastic)

(defvar plastic-lit-string 
  ">" 
  "*Prefix of literate lines. Set to empty string to get non-literate mode")

(defcustom plastic-help-menu-list
  '(["The PLASTIC Reference Card" (browse-url plastic-www-refcard) t]
    ["The PLASTIC library (WWW)" (browse-url plastic-library-www-page)  t])
  "List of menu items, as defined in `easy-menu-define' for Plastic
  specific help."
  :type '(repeat sexp)
  :group 'plastic)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Configuration of Generic Proof Package ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Users should not need to change this. 

(defvar plastic-shell-process-output
  '((lambda (cmd string) (proof-string-match "^Module" cmd)) .
    (lambda (cmd string)
      (setq proof-shell-delayed-output
	    ;;FIXME: This should be displayed in the minibuffer only
	    (cons 'insert "\n\nImports done!"))))
  "Acknowledge end of processing import declarations.")

(defconst plastic-process-config 
  (concat plastic-lit-string 
	  " &S ECHO No PrettyPrinting configuration implemented;\n")
  "Command to enable pretty printing of the Plastic process.
   Proof-General annotations triggered by a cmd-line opt
  ")

(defconst plastic-pretty-set-width "&S ECHO no PrettyWidth ;\n"
  "Command to adjust the linewidth for pretty printing of the Plastic
  process.") 

(defconst plastic-interrupt-regexp "Interrupt.."
  "Regexp corresponding to an interrupt")


;; ----- web documentation

(defcustom plastic-www-home-page "http://www.dur.ac.uk/CARG/plastic.html"
  "Plastic home page URL."
  :type 'string
  :group 'plastic)

(defcustom plastic-www-latest-release
  (concat plastic-www-home-page "/current")
  "The WWW address for the latest Plastic release."
  :type 'string
  :group 'plastic)
	  
(defcustom plastic-www-refcard
  plastic-www-home-page
  "URL for the Plastic reference card."
  :type 'string
  :group 'plastic)

(defcustom plastic-library-www-page
  (concat plastic-www-home-page "/library")
  "The HTML documentation of the Plastic library."
  :type 'string
  :group 'plastic)



;; ----- plastic-shell configuration options

(defvar plastic-base 
  "PLASTIC_BASE:TO_BE_CUSTOMISED"
  "*base dir of plastic distribution")

(defvar plastic-prog-name 
  (concat plastic-base "/plastic")
  "*Name of program to run as plastic.")

(defun plastic-set-default-env-vars ()
  "defaults for the expected lib vars."
  (cond 
    ((not (getenv "PLASTIC_LIB"))
		(setenv "PLASTIC_LIB" (concat plastic-base "/lib"))
		(setenv "PLASTIC_TEST" (concat plastic-base "/test"))
	)))

(defvar plastic-shell-prompt-pattern "^\\(LF>[ \201]*\\)+"
  "*The prompt pattern for the inferior shell running plastic.")

(defvar plastic-shell-cd 
  (concat plastic-lit-string " &S ECHO no cd ;\n")
  "*Command of the inferior process to change the directory.") 

(defvar plastic-shell-abort-goal-regexp "KillRef: ok, not in proof state"
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(defvar plastic-shell-proof-completed-regexp "\\*\\*\\* QED \\*\\*\\*"
  "*Regular expression indicating that the proof has been completed.")

(defvar plastic-save-command-regexp
  (concat "^" (proof-ids-to-regexp plastic-keywords-save)))
(defvar plastic-goal-command-regexp
  (concat "^" (proof-ids-to-regexp plastic-keywords-goal)))

(defvar plastic-kill-goal-command 
  (concat plastic-lit-string " &S ECHO KillRef not applicable;"))
(defvar plastic-forget-id-command 
  (concat plastic-lit-string " &S Forget "))

(defvar plastic-undoable-commands-regexp
  (proof-ids-to-regexp '("Refine" "Intros" "intros" "Normal" "Claim" "Immed"))
  "Undoable list")

;; "Dnf" "Refine" "Intros" "intros" "Next" "Normal"
;;   "Qrepl" "Claim" "For" "Repeat" "Succeed" "Fail" "Try" "Assumption"
;;   "UTac" "Qnify" "qnify" "andE" "andI" "exE" "exI" "orIL" "orIR" "orE" "ImpI"
;;   "impE" "notI" "notE" "allI" "allE" "Expand" "Induction" "Immed"
;;   "Invert"

;; ----- outline

(defvar plastic-goal-regexp "\\?\\([0-9]+\\)")

(defvar plastic-outline-regexp
  (concat "[[*]\\|"
	  (proof-ids-to-regexp 
	   '("Discharge" "DischargeKeep" "Freeze" "$?Goal" "Module" "Record" "Inductive"
     "Unfreeze"))))

(defvar plastic-outline-heading-end-regexp ";\\|\\*)")

(defvar plastic-shell-outline-regexp plastic-goal-regexp)
(defvar plastic-shell-outline-heading-end-regexp plastic-goal-regexp)

(defvar plastic-error-occurred 
        nil
        "flag for whether undo is required for try or minibuffer cmds")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-derived-mode plastic-shell-mode proof-shell-mode
   "plastic-shell"
   ;; With nil argument for docstring, Emacs makes up a nice one.
   nil
   (plastic-shell-mode-config))

(define-derived-mode plastic-mode proof-mode
   "plastic" 
   nil
   (plastic-mode-config)
   (easy-menu-change (list proof-general-name) (car proof-help-menu)
		     (append (cdr proof-help-menu) plastic-help-menu-list)))

(eval-and-compile
  (define-derived-mode plastic-response-mode proof-response-mode
    "PlasticResp" nil
    (setq font-lock-keywords plastic-font-lock-terms)
    (plastic-init-syntax-table)
    (proof-response-config-done)))
  
(define-derived-mode plastic-pbp-mode pbp-mode
  "PlasticGoals" "Plastic Goal State"
  (plastic-pbp-mode-config))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's plastic specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun plastic-count-undos (span)
  "This is how to work out what the undo commands are.
Given is the first SPAN which needs to be undone."
  (let ((ct 0) string i)
    (while span
      (setq string (span-property span 'cmd))
      (plastic-preprocessing)			;; dynamic scope, on string
      (cond ((eq (span-property span 'type) 'vanilla)
	     (if (or (proof-string-match plastic-undoable-commands-regexp string)
		     (and (proof-string-match "Equiv" string)
			  (not (proof-string-match "Equiv\\s +[TV]Reg" string))))
		 (setq ct (+ 1 ct))))
	    ((eq (span-property span 'type) 'pbp)
	     (setq i 0)
	     (while (< i (length string)) 
	       (if (= (aref string i) proof-terminal-char) (setq ct (+ 1 ct)))
	       (setq i (+ 1 i)))))
      (setq span (next-span span 'type)))
    (concat plastic-lit-string " &S Undo x" (int-to-string ct) proof-terminal-string)))

(defun plastic-goal-command-p (str)
  "Decide whether argument is a goal or not"			;; NEED CHG.
  (proof-string-match plastic-goal-command-regexp str))

(defun plastic-find-and-forget (span) 
	;; count the number of spans to undo.
	;; all spans are equal...
    ;; (NB the 'x' before the id is required so xNN looks like an id, 
    ;;  so that Undo can be implemented via the tmp_cmd route.)
  (let (string (spans 0))
    (while span
      (setq string (span-property span 'cmd))
      (plastic-preprocessing)		;; dynamic scope, on string

      (cond
         ((null string) nil)
         ((or (string-match "^\\s-*import" string) 
	      (string-match "^\\s-*test" string)
	      (string-match "^\\s-*\\$" string)
	      (string-match "^\\s-*#" string))
               (if (yes-or-no-p-dialog-box 
                           (concat "Can't Undo imports yet\n"
                                   "You have to exit prover for this\n"
                                   "Continue with Exit?"))
                   (proof-shell-exit)
                   nil) )	;; see if the user wants to quit.
         (t (incf spans))
      )
      (setq span (next-span span 'type))

    )
    (concat plastic-lit-string " &S Undo x" (int-to-string spans) proof-terminal-string) ))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Other stuff which is required to customise script management   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun plastic-goal-hyp ()		;; not used.
  (cond 
   ((looking-at plastic-goal-regexp)
    (cons 'goal (match-string 1)))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))


;; NEED TO REFINE THIS (may99)

(defun plastic-state-preserving-p (cmd)
  (not (proof-string-match plastic-undoable-commands-regexp cmd)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to plastic                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun plastic-intros ()
  "intros."
  (interactive)
  (insert (concat plastic-lit-string " intros ")))

(defun plastic-Intros () 
  "List proof state." 
  (interactive) 
  (insert (concat plastic-lit-string " Intros ")))

(defun plastic-Refine () 
  "List proof state."  
  (interactive) 
  (insert (concat plastic-lit-string " Refine ")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Plastic Indentation                                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun plastic-stack-to-indent (stack)
  (cond
   ((null stack) 0)
   ((null (car (car stack)))
    (nth 1 (car stack)))
   (t (save-excursion
	(goto-char (nth 1 (car stack)))
	(+ plastic-indent (current-column))))))

(defun plastic-parse-indent (c stack)
  (cond
   ((eq c ?\{) (cons (list c (point)) stack))
   ((eq c ?\}) (cdr stack))
   (t stack)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Plastic shell startup and exit hooks                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar plastic-shell-current-line-width nil
  "Current line width of the Plastic process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;; The line width needs to be adjusted if the PLASTIC process is
;; running and is out of sync with the screen width

(defun plastic-shell-adjust-line-width ()
  "Use Plastic's pretty printing facilities to adjust output line width.
   Checks the width in the `proof-goals-buffer' 
   ACTUALLY - still need to work with this. (pcc, may99)"
   (and (buffer-live-p proof-goals-buffer)
        (proof-shell-live-buffer)
        (save-excursion
        (set-buffer proof-goals-buffer)
        (let ((current-width
               ;; Actually, one might sometimes
               ;; want to get the width of the proof-response-buffer
               ;; instead. Never mind.
               (window-width (get-buffer-window proof-goals-buffer))))

	   (if (equal current-width plastic-shell-current-line-width) ()
	     ; else
	     (setq plastic-shell-current-line-width current-width)
	     (set-buffer proof-shell-buffer)
	     (insert (format plastic-pretty-set-width (- current-width 1)))
	     )))))

(defun plastic-pre-shell-start ()
  (setq proof-prog-name (concat plastic-prog-name "")
        ;; set cmd-line flag 
        proof-mode-for-shell 'plastic-shell-mode
        proof-mode-for-response 'plastic-response-mode
        proof-mode-for-pbp 'plastic-pbp-mode)

  (setenv "PROOF_GENERAL" "")		;; signal to plastic, use annotations
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun plastic-mode-config ()
  ;; da: this is now a user-option, please set it in your .emacs
  ;; via customize mechanism.
  ;; (setq proof-electric-terminator-enable t)	;; force semicolons active.

  (setq proof-terminal-char ?\;)
  (setq proof-comment-start "(*")			;; these still active
  (setq proof-comment-end "*)")

  (setq proof-assistant-home-page plastic-www-home-page)
  (setq proof-mode-for-script 'plastic-mode)

  (setq proof-showproof-command (concat plastic-lit-string " &S PrfCtxt")
	proof-goal-command      (concat plastic-lit-string " Claim %s;")
	proof-save-command      (concat plastic-lit-string " Save %s;") ;; analogue? 
	proof-context-command   (concat plastic-lit-string " &S Ctxt 20"))

  (setq proof-showproof-command  (concat plastic-lit-string " &S PrfCtxt")
	proof-goal-command   (concat plastic-lit-string " Claim %s;")
	proof-save-command   (concat plastic-lit-string " Save %s;") ;; analogue? 
	proof-context-command  (concat plastic-lit-string " &S Ctxt 20")
	   ;; show 20 things; see ^c+C...
	proof-info-command   (concat plastic-lit-string " &S Help"))

  (setq proof-goal-command-p 'plastic-goal-command-p
	proof-count-undos-fn 'plastic-count-undos
	proof-find-and-forget-fn 'plastic-find-and-forget
        proof-goal-hyp-fn 'plastic-goal-hyp
	proof-state-preserving-p 'plastic-state-preserving-p
	proof-parse-indent 'plastic-parse-indent
	proof-stack-to-indent 'plastic-stack-to-indent)

  (setq	proof-save-command-regexp plastic-save-command-regexp
	proof-goal-command-regexp plastic-goal-command-regexp
	proof-save-with-hole-regexp plastic-save-with-hole-regexp
	proof-goal-with-hole-regexp plastic-goal-with-hole-regexp
	proof-kill-goal-command plastic-kill-goal-command
	proof-indent-commands-regexp (proof-ids-to-regexp plastic-commands))

  (plastic-init-syntax-table)

  ;; da: I've moved these out of proof-config-done in proof-script.el 
  (setq pbp-goal-command (concat "UNIMPLEMENTED"))
  (setq pbp-hyp-command (concat "UNIMPLEMENTED"))

;; font-lock

  (setq font-lock-keywords plastic-font-lock-keywords-1)

;; FIXME da: this is done generically now.  If you want
;; the zap commas behaviour, set proof-font-lock-zap-commas=t here.
;;  (and (boundp 'font-lock-always-fontify-immediately)
;;       (setq font-lock-always-fontify-immediately t))


  (proof-config-done)

  (define-key (current-local-map) [(control c) ?i] 'plastic-intros)
  (define-key (current-local-map) [(control c) ?I] 'plastic-Intros)
  (define-key (current-local-map) [(control c) ?r] 'plastic-Refine)

;; pcc macros etc

  (define-key (current-local-map) [(control c) ?s] 'plastic-small-bar)
  (define-key (current-local-map) [(control c) ?l] 'plastic-large-bar)
  (define-key (current-local-map) [(control c) ?a] 'plastic-all-ctxt)

;; pcc over-ride the try-cmd fn

  (define-key (current-local-map) [(control c) (control t)] 'plastic-try-cmd)
  (define-key (current-local-map) [(control c) (control v)] 'plastic-minibuf)
  (define-key (current-local-map) [(control c) (control o)] 'plastic-synchro)
  (define-key (current-local-map) [(control c) (control s)] 'plastic-show-shell)

;; outline
  
  (make-local-variable 'outline-regexp)
  (setq outline-regexp plastic-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp plastic-outline-heading-end-regexp)

;; tags
  (cond ((boundp 'tags-table-list)
	 (make-local-variable 'tags-table-list)
	 (setq tags-table-list (cons plastic-tags tags-table-list))))

  (and (boundp 'tag-table-alist)
       (setq tag-table-alist
	     (append '(("\\.lf$"   . plastic-tags)
		       ("plastic"  . plastic-tags))
		     tag-table-alist)))

  (setq blink-matching-paren-dont-ignore-comments t)

;; hooks and callbacks

  (add-hook 'proof-pre-shell-start-hook    'plastic-pre-shell-start nil t)
  (add-hook 'proof-shell-insert-hook       'plastic-shell-adjust-line-width)
  (add-hook 'proof-shell-handle-error-or-interrupt-hook 'plastic-had-error)
  (add-hook 'proof-shell-insert-hook       'plastic-preprocessing)

;; (add-hook 'proof-shell-handle-error-or-interrupt-hook 
;; (lambda()(goto-char (search-forward (char-to-string  proof-terminal-char)))))

;;  (add-hook 'proof-shell-handle-delayed-output-hook `plastic-show-shell-buffer t)
;; this forces display of shell-buffer after each cmd, rather than goals-buffer
;; it is not always necessary - could always add it as a toggle option? 

;; set up the env.
  (plastic-set-default-env-vars)
  )

(defun plastic-show-shell-buffer ()
   "switch buffers."
   (display-buffer proof-shell-buffer)
   )


(defun plastic-equal-module-filename (module filename)
  "Returns `t' if MODULE is equal to the FILENAME and `nil' otherwise.
The directory and extension is stripped of FILENAME before the test."
  (equal module
	 (file-name-sans-extension (file-name-nondirectory filename))))

(defun plastic-shell-compute-new-files-list (str)
  "Function to update `proof-included-files list'.

It needs to return an up to date list of all processed files. Its
output is stored in `proof-included-files-list'. Its input is the
string of which `plastic-shell-retract-files-regexp' matched a
substring. 

We assume that module identifiers coincide with file names."
  (let ((module (match-string 1 str)))
    (cdr (member-if
	  (lambda (filename) (plastic-equal-module-filename module filename))
	  proof-included-files-list))))



(defun plastic-shell-mode-config ()
  (setq proof-shell-prompt-pattern plastic-shell-prompt-pattern
        proof-shell-cd-cmd plastic-shell-cd
        proof-shell-abort-goal-regexp plastic-shell-abort-goal-regexp
        proof-shell-proof-completed-regexp plastic-shell-proof-completed-regexp
        proof-shell-error-regexp plastic-error-regexp
        proof-shell-interrupt-regexp plastic-interrupt-regexp
        ;; DEAD proof-shell-noise-regexp "Discharge\\.\\. "
        proof-shell-assumption-regexp plastic-id
        proof-shell-goal-regexp plastic-goal-regexp
        proof-shell-first-special-char ?\360
        proof-shell-wakeup-char ?\371		;; only for first send? 
;;      proof-shell-wakeup-char nil		;; NIL turns off annotations.
        proof-shell-start-char ?\372
        proof-shell-end-char ?\373
        proof-shell-field-char ?\374
        proof-shell-goal-char ?\375
        proof-shell-eager-annotation-start "\376"
	;; FIXME da: if p-s-e-a-s is implemented, you should set
	;; proof-shell-eager-annotation-start-length=1 to
	;; avoid possibility of duplicating short messages.
        proof-shell-eager-annotation-end "\377"

        proof-shell-annotated-prompt-regexp "LF> \371"
        proof-shell-result-start "\372 Pbp result \373"
        proof-shell-result-end "\372 End Pbp result \373"
        proof-shell-start-goals-regexp "\372 Start of Goals \373"
        proof-shell-end-goals-regexp "\372 End of Goals \373"

        proof-shell-init-cmd plastic-process-config
	proof-shell-restart-cmd plastic-process-config
        proof-analyse-using-stack nil
        proof-shell-process-output-system-specific plastic-shell-process-output
        plastic-shell-current-line-width nil

	proof-shell-process-file
	(cons "Creating mark \"\\(.*\\)\" \\[\\(.*\\)\\]"  
	  (lambda (str) (let ((match (match-string 2 str)))
			  (if (equal match "") match
			    (concat (file-name-sans-extension match) ".l")))))

	proof-shell-retract-files-regexp "forgot back through Mark \"\\(.*\\)\""
	font-lock-keywords plastic-font-lock-keywords-1

	proof-shell-compute-new-files-list 'plastic-shell-compute-new-files-list)

  (plastic-init-syntax-table)

  (proof-shell-config-done)
  )

(defun plastic-pbp-mode-config ()
  (setq pbp-change-goal "Next %s;"
        pbp-error-regexp plastic-error-regexp)
  (setq font-lock-keywords plastic-font-lock-terms)
  (plastic-init-syntax-table)
  (proof-goals-config-done))



;;;;;;;;;;;;;;;;;
;; MY new additions.

(defun plastic-small-bar () (interactive) (insert "%------------------------------\n"))

(defun plastic-large-bar () (interactive) (insert "%-------------------------------------------------------------------------------\n"))

(defun plastic-preprocessing () 
   "clear comments and remove literate marks (ie, \\n> ) - acts on var string"

   ;; might want to use proof-string-match here if matching is going to be
   ;; case sensitive (see docs)

   (if (= 0 (length plastic-lit-string)) 
	string		;; no-op if non-literate

			;; remaining lines are the Else. (what, no 'return'?)
   (setq string (concat "\n" string " "))   ;; seed routine below, & extra char
   (let* ;; da: let* not really needed, added to nuke byte-comp warnings. 
     ( (i 0)
       (l (length string))
       (eat-rest (lambda () 
                    (aset string i ?\ )  ;; kill the \n or "-" at least
                    (incf i)
                    (while (and (< i l) (/= (aref string i) ?\n))
                           (aset string i ?\ )
                           (incf i) )))
       (keep-rest (lambda () 
                    (loop for x in (string-to-list plastic-lit-string)
                          do (aset string i ?\ ) (incf i))
                    (while (and (< i l) 
                                (/= (aref string i) ?\n)
                                (/= (aref string i) ?-))
                           (incf i) )))
   )
   (while (< i l)
          (cond
               ((eq 0 (string-match "--" (substring string i)))
                   (funcall eat-rest))           ;; comment.
               ((eq 0 (string-match "\n\n" (substring string i)))
                   (aset string i ?\ ) 
                   (incf i)) ;; kill repeat \n

               ((= (aref string i) ?\n)		;; start of new line
                   (aset string i ?\ ) (incf i) ;; remove \n

	               (if (eq 0 (string-match plastic-lit-string 
					         (substring string i)))
                       (funcall keep-rest)       ;; code line.
                       (funcall eat-rest)        ;; non-code line
                   ))

               (t (incf i))                      ;; else include.
            )
   )
   (setq string (replace-in-string string "  *" " "))
   (setq string (replace-in-string string "^ *" ""))
   (if (string-match "^\\s-*$" string)
       (setq string (concat "ECHO comment line" proof-terminal-string))
       string)
   )))


(defun plastic-all-ctxt () 
	"show the full ctxt"
	(interactive)
	(proof-shell-invisible-command 
              (concat plastic-lit-string " &S Ctxt" proof-terminal-string))
	)

(defun plastic-send-one-undo ()
	"send an Undo cmd"
    ;; FIXME da IMPORTANT: please use proof-shell-invisible-command
    ;; instead here, or tell me why you can't if it doesn't work.
    ;; Interface to proof-shell-insert now requires two args (for the
    ;; sake of plastic!) and shouldn't be called from PG instances 
    (proof-shell-insert (concat plastic-lit-string " &S Undo;")
			'proof-done-invisible))

(defun plastic-try-cmd ()
    "undo whatever was tried, if error-free"
    (interactive)
    (plastic-reset-error)
    (let ((proof-state-preserving-p nil)) ; allow any command
      (call-interactively 'proof-minibuffer-cmd))
    (plastic-call-if-no-error 'plastic-send-one-undo))

(defun plastic-minibuf ()
    "do minibuffer cmd then undo it, if error-free."
    (interactive)
    (plastic-reset-error)
    (plastic-send-minibuf)
    (plastic-call-if-no-error 'plastic-send-one-undo))

(defun plastic-synchro ()
    "do minibuffer cmd BUT DON'T UNDO IT - use if things go wrong!"
    (interactive)
    (plastic-send-minibuf))

(defun plastic-send-minibuf ()
    "take cmd from minibuffer - see doc for proof-minibuffer-cmd"
    (interactive)
    (let (cmd)
        (setq cmd (read-string "Command: " nil 'proof-minibuffer-history))
        (setq cmd (concat plastic-lit-string " " cmd proof-terminal-string))
        (proof-shell-invisible-command cmd)))

(defun plastic-had-error ()
    "sets var plastic-error-occurred, called from hook"
    (if (eq proof-shell-error-or-interrupt-seen 'error)
	(setq plastic-error-occurred t)))
(defun plastic-reset-error ()
    "UNsets var plastic-error-occurred, before minibuffer or try cmd"
    (setq plastic-error-occurred nil))
(defun plastic-call-if-no-error (fn)
    "wait for proof process to be idle, and call fn if error-free."
    (while proof-shell-busy (sleep-for 0.25))
    (if (not plastic-error-occurred) (funcall fn)))

(defun plastic-show-shell ()
    "shortcut to shell buffer"
    (interactive)
    (proof-switch-to-buffer proof-shell-buffer))

;; original end.

(provide 'plastic)
