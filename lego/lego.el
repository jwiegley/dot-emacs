;; lego.el Major mode for LEGO proof assistants
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Author:      Thomas Kleymann and Dilip Sequeira
;; Maintainer: Paul Callaghan <P.C.Callaghan@durham.ac.uk>

;;
;; $Id$
;;

(require 'proof)
(require 'proof-script)

;;FIXME: proof-shell should be autoloaded
(require 'proof-shell)
(require 'lego-syntax)

;; FIXME: outline should be autoloaded
(require 'outline)

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User Configuration ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I believe this is standard for Linux under RedHat -tms
(defcustom lego-tags "/usr/lib/lego/lib_Type/"
  "*The directory of the TAGS table for the LEGO library"
  :type 'file
  :group 'lego)

(defcustom lego-indent 2
  "*Indentation"
  :type 'number
  :group 'lego)

(defcustom lego-test-all-name "test_all"
  "*The name of the LEGO module which inherits all other modules of the
  library."
  :type 'string
  :group 'lego)

(defcustom lego-help-menu-list
  '(["The LEGO Reference Card" (browse-url lego-www-refcard) t]
    ["The LEGO library (WWW)" (browse-url lego-library-www-page)  t])
  "List of menu itemsfor LEGO specific help.

See the documentation of `easy-menu-define' "
  :type '(repeat sexp)
  :group 'lego)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Configuration of Generic Proof Package ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Users should not need to change this. 

(defvar lego-shell-process-output
  '((lambda (cmd string) (proof-string-match "^Module" cmd)) .
    (lambda (cmd string)
      (setq proof-shell-delayed-output
	    ;;FIXME: This should be displayed in the minibuffer only
	    (cons 'insert "\n\nImports done!"))))
  "Acknowledge end of processing import declarations.")

(defconst lego-process-config
  "Init XCC; Configure PrettyOn; Configure AnnotateOn;"
  "Command to initialise the LEGO process.

Initialises empty context and prepares XCC theory.
Enables pretty printing.
Activates extended printing routines required for Proof General.")

(defconst lego-pretty-set-width "Configure PrettyWidth %s; "
  "Command to adjust the linewidth for pretty printing of the LEGO
  process.") 

(defconst lego-interrupt-regexp "Interrupt.."
  "Regexp corresponding to an interrupt")

;; ----- web documentation

(defcustom lego-www-home-page "http://www.dcs.ed.ac.uk/home/lego/"
  "Lego home page URL."
  :type 'string
  :group 'lego)

(defcustom lego-www-latest-release
  "http://www.dcs.ed.ac.uk/home/lego/html/release-1.3.1/"
  "The WWW address for the latest LEGO release."
  :type 'string
  :group 'lego)
	  
(defcustom lego-www-refcard
  (concat lego-www-latest-release "refcard.ps.gz")
  "URL for the Lego reference card."
  :type 'string
  :group 'lego)

(defcustom lego-library-www-page
  (concat lego-www-latest-release "library/library.html")
  "The HTML documentation of the LEGO library."
  :type 'string
  :group 'lego)


;; ----- lego-shell configuration options

(defvar lego-prog-name "lego"
  "*Name of program to run as lego.")

(defvar lego-shell-prompt-pattern "^\\(Lego>[ \201]*\\)+"
  "*The prompt pattern for the inferior shell running lego.")

(defvar lego-shell-cd "Cd \"%s\";"
  "*Command of the inferior process to change the directory.") 

(defvar lego-shell-abort-goal-regexp "KillRef: ok, not in proof state"
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(defvar lego-shell-proof-completed-regexp "\\(\\*\\*\\* QED \\*\\*\\*\\)"
  "*Regular expression indicating that the proof has been completed.")

(defvar lego-save-command-regexp
  (concat "^" (proof-ids-to-regexp lego-keywords-save)))
(defvar lego-goal-command-regexp
  (concat "^" (proof-ids-to-regexp lego-keywords-goal)))

(defvar lego-kill-goal-command "KillRef;")
(defvar lego-forget-id-command "Forget ")

(defvar lego-undoable-commands-regexp
  (proof-ids-to-regexp '("Dnf" "Refine" "Intros" "intros" "Next" "Normal"
  "Qrepl" "Claim" "For" "Repeat" "Succeed" "Fail" "Try" "Assumption"
  "UTac" "Qnify" "qnify" "andE" "andI" "exE" "exI" "orIL" "orIR" "orE" "ImpI"
  "impE" "notI" "notE" "allI" "allE" "Expand" "Induction" "Immed"
  "Invert")) "Undoable list")

;; ----- outline

(defvar lego-goal-regexp "\\?\\([0-9]+\\)")

(defvar lego-outline-regexp
  (concat "[[*]\\|"
	  (proof-ids-to-regexp 
	   '("Discharge" "DischargeKeep" "Freeze" "$?Goal" "Module" "Record" "Inductive"
     "Unfreeze"))))

(defvar lego-outline-heading-end-regexp ";\\|\\*)")

(defvar lego-shell-outline-regexp lego-goal-regexp)
(defvar lego-shell-outline-heading-end-regexp lego-goal-regexp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-derived-mode lego-shell-mode proof-shell-mode
   "lego-shell"
   ;; With nil argument for docstring, Emacs makes up a nice one.
   nil
   (lego-shell-mode-config))

(define-derived-mode lego-mode proof-mode
   "lego" nil
   (lego-mode-config)
   (easy-menu-change (list proof-general-name) (car proof-help-menu)
		     (append (cdr proof-help-menu) lego-help-menu-list)))

(eval-and-compile
  (define-derived-mode lego-response-mode proof-response-mode
    "LEGOResp" nil
    (setq font-lock-keywords lego-font-lock-terms)
    (lego-init-syntax-table)
    (proof-response-config-done)))
  
(define-derived-mode lego-pbp-mode pbp-mode
  "LEGOGoals" "LEGO Proof State"
  (lego-pbp-mode-config))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's lego specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; needs to handle Normal as well
;; it should ignore Normal TReg Normal VReg and (Normal ...)
(defun lego-count-undos (span)
  "This is how to work out what the undo commands are.
Given is the first SPAN which needs to be undone."
  (let ((ct 0) str i)
    (while span
      (setq str (span-property span 'cmd))
      (cond ((eq (span-property span 'type) 'vanilla)
	     (if (or (proof-string-match lego-undoable-commands-regexp str)
		     (and (proof-string-match "Equiv" str)
			  (not (proof-string-match "Equiv\\s +[TV]Reg" str))))
		 (setq ct (+ 1 ct))))
	    ((eq (span-property span 'type) 'pbp)
	     (setq i 0)
	     (while (< i (length str)) 
	       (if (= (aref str i) proof-terminal-char) (setq ct (+ 1 ct)))
	       (setq i (+ 1 i)))))
      (setq span (next-span span 'type)))
    (concat "Undo " (int-to-string ct) proof-terminal-string)))

(defun lego-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (proof-string-match lego-goal-command-regexp str))

(defun lego-find-and-forget (span) 
  (let (str ans)
    (while (and span (not ans))
      (setq str (span-property span 'cmd))
      
      (cond
       
       ((eq (span-property span 'type) 'comment))

       ((eq (span-property span 'type) 'goalsave)
	(setq ans (concat lego-forget-id-command
			  (span-property span 'name) proof-terminal-string)))

       ;; alternative definitions
       ((proof-string-match lego-definiendum-alternative-regexp str)
	(setq ans (concat lego-forget-id-command (match-string 1 str)
			  proof-terminal-string)))
       ;; declarations
       ((proof-string-match (concat "\\`\\$?" (lego-decl-defn-regexp "[:|=]")) str)
	(let ((ids (match-string 1 str))) ; returns "a,b"
	  (proof-string-match proof-id ids)	; matches "a"
	  (setq ans (concat lego-forget-id-command(match-string 1 ids)
			    proof-terminal-string))))
	   
       ((proof-string-match "\\`\\(Inductive\\|\\Record\\)\\s-*\\[\\s-*\\w+\\s-*:[^;]+\\`Parameters\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans (concat lego-forget-id-command
			  (match-string 2 str) proof-terminal-string)))

       ((proof-string-match 
	 "\\`\\(Inductive\\|Record\\)\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans 
	      (concat lego-forget-id-command (match-string 2 str)
		      proof-terminal-string)))
       
       ((proof-string-match "\\`\\s-*Module\\s-+\\(\\S-+\\)\\W" str)
	(setq ans (concat "ForgetMark " (match-string 1 str) 
			  proof-terminal-string))))
      
      (setq span (next-span span 'type)))
  (or ans proof-no-command)))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Other stuff which is required to customise script management   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-goal-hyp ()
  (cond 
   ((looking-at lego-goal-regexp)
    (cons 'goal (match-string 1)))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))


(defun lego-state-preserving-p (cmd)
  (not (proof-string-match lego-undoable-commands-regexp cmd)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to lego                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-intros ()
  "intros."
  (interactive)
  (insert "intros "))

(defun lego-Intros () 
  "List proof state." 
  (interactive) 
  (insert "Intros "))

(defun lego-Refine () 
  "List proof state."  
  (interactive) 
  (insert "Refine "))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Lego Indentation                                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-stack-to-indent (stack)
  (cond
   ((null stack) 0)
   ((null (car (car stack)))
    (nth 1 (car stack)))
   (t (save-excursion
	(goto-char (nth 1 (car stack)))
	(+ lego-indent (current-column))))))

(defun lego-parse-indent (c stack)
  (cond
   ((eq c ?\{) (cons (list c (point)) stack))
   ((eq c ?\}) (cdr stack))
   (t stack)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Lego shell startup and exit hooks                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar lego-shell-current-line-width nil
  "Current line width of the LEGO process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;; The line width needs to be adjusted if the LEGO process is
;; running and is out of sync with the screen width

(defun lego-shell-adjust-line-width ()
  "Use LEGO's pretty printing facilities to adjust output line width.
Checks the width in the `proof-goals-buffer'"
  (and (buffer-live-p proof-goals-buffer)
       (proof-shell-live-buffer)
       (save-excursion 
	 (set-buffer proof-goals-buffer)
	 (let ((current-width
		;; Actually, one might sometimes
		;; want to get the width of the proof-response-buffer
		;; instead. Never mind. 
		(window-width (get-buffer-window proof-goals-buffer))))
	   (if (equal current-width lego-shell-current-line-width) ()
	     ; else
	     (setq lego-shell-current-line-width current-width)
	     (set-buffer proof-shell-buffer)
	     (insert (format lego-pretty-set-width (- current-width 1)))
	     )))))

(defun lego-pre-shell-start ()
  (setq proof-prog-name lego-prog-name
	proof-mode-for-shell 'lego-shell-mode
	proof-mode-for-response 'lego-response-mode
	proof-mode-for-pbp 'lego-pbp-mode))


(defun lego-mode-config ()

  (setq proof-terminal-char ?\;)
  (setq proof-comment-start "(*")
  (setq proof-comment-end "*)")

  (setq proof-assistant-home-page lego-www-home-page)

  (setq proof-mode-for-script 'lego-mode)

  (setq proof-prf-string "Prf"
	proof-goal-command "Goal %s;"
	proof-save-command "Save %s;"
	proof-ctxt-string "Ctxt"
	proof-help-string "Help")

  (setq proof-goal-command-p 'lego-goal-command-p
	proof-count-undos-fn 'lego-count-undos
	proof-find-and-forget-fn 'lego-find-and-forget
        proof-goal-hyp-fn 'lego-goal-hyp
	proof-state-preserving-p 'lego-state-preserving-p
	proof-parse-indent 'lego-parse-indent
	proof-stack-to-indent 'lego-stack-to-indent)

  (setq	proof-save-command-regexp lego-save-command-regexp
	proof-goal-command-regexp lego-goal-command-regexp
	proof-save-with-hole-regexp lego-save-with-hole-regexp
	proof-goal-with-hole-regexp lego-goal-with-hole-regexp
	proof-kill-goal-command lego-kill-goal-command
	proof-indent-commands-regexp (proof-ids-to-regexp lego-commands))

  (lego-init-syntax-table)

  ;; da: I've moved these out of proof-config-done in proof-script.el 
  (setq pbp-goal-command (concat "Pbp %s" proof-terminal-string))
  (setq pbp-hyp-command (concat "PbpHyp %s" proof-terminal-string))

  (proof-config-done)

  (define-key (current-local-map) [(control c) ?i] 'lego-intros)
  (define-key (current-local-map) [(control c) ?I] 'lego-Intros)
  (define-key (current-local-map) [(control c) ?r] 'lego-Refine)

;; outline
  
  (make-local-variable 'outline-regexp)
  (setq outline-regexp lego-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp lego-outline-heading-end-regexp)

;; tags
  (cond ((boundp 'tags-table-list)
	 (make-local-variable 'tags-table-list)
	 (setq tags-table-list (cons lego-tags tags-table-list))))

  (and (boundp 'tag-table-alist)
       (setq tag-table-alist
	     (append '(("\\.l$" . lego-tags)
		       ("lego"  . lego-tags))
		     tag-table-alist)))

  (setq blink-matching-paren-dont-ignore-comments t)

;; font-lock

  (setq font-lock-keywords lego-font-lock-keywords-1)

;; if we don't have the following in xemacs, zap-commas fails to work.

  (and (boundp 'font-lock-always-fontify-immediately)
       (setq font-lock-always-fontify-immediately t))

;; hooks and callbacks

  (add-hook 'proof-pre-shell-start-hook 'lego-pre-shell-start nil t)
  (add-hook 'proof-shell-insert-hook 'lego-shell-adjust-line-width))

(defun lego-equal-module-filename (module filename)
  "Returns `t' if MODULE is equal to the FILENAME and `nil' otherwise.
The directory and extension is stripped of FILENAME before the test."
  (equal module
	 (file-name-sans-extension (file-name-nondirectory filename))))

(defun lego-shell-compute-new-files-list (str)
  "Function to update `proof-included-files list'.

It needs to return an up to date list of all processed files. Its
output is stored in `proof-included-files-list'. Its input is the
string of which `lego-shell-retract-files-regexp' matched a
substring. 

We assume that module identifiers coincide with file names."
  (let ((module (match-string 1 str)))
    (cdr (member-if
	  (lambda (filename) (lego-equal-module-filename module filename))
	  proof-included-files-list))))

(defun lego-shell-mode-config ()
  (setq proof-shell-prompt-pattern lego-shell-prompt-pattern
        proof-shell-cd lego-shell-cd
        proof-shell-abort-goal-regexp lego-shell-abort-goal-regexp
        proof-shell-proof-completed-regexp lego-shell-proof-completed-regexp
        proof-shell-error-regexp lego-error-regexp
	proof-shell-interrupt-regexp lego-interrupt-regexp
        proof-shell-assumption-regexp lego-id
        proof-shell-first-special-char ?\360
        proof-shell-wakeup-char ?\371
        proof-shell-start-char ?\372
        proof-shell-end-char ?\373
        proof-shell-field-char ?\374
        proof-shell-goal-char ?\375
	proof-shell-eager-annotation-start "\376"
	proof-shell-eager-annotation-end "\377"
        proof-shell-annotated-prompt-regexp "Lego> \371"
        proof-shell-result-start "\372 Pbp result \373"
        proof-shell-result-end "\372 End Pbp result \373"
        proof-shell-start-goals-regexp "\372 Start of Goals \373"
        proof-shell-end-goals-regexp "\372 End of Goals \373"
        proof-shell-init-cmd lego-process-config
	proof-shell-restart-cmd lego-process-config
	proof-analyse-using-stack nil
	proof-shell-process-output-system-specific lego-shell-process-output
        lego-shell-current-line-width nil

	proof-shell-process-file
	(cons "Creating mark \"\\(.*\\)\" \\[\\(.*\\)\\]"  
	  (lambda (str) (let ((match (match-string 2 str)))
			  (if (equal match "") match
			    (concat (file-name-sans-extension match) ".l")))))

	proof-shell-retract-files-regexp
	"forgot back through Mark \"\\(.*\\)\""
	font-lock-keywords lego-font-lock-keywords-1

	proof-shell-compute-new-files-list 
	'lego-shell-compute-new-files-list)

  (lego-init-syntax-table)

  (proof-shell-config-done))

(defun lego-pbp-mode-config ()
  (setq pbp-change-goal "Next %s;"
	pbp-error-regexp lego-error-regexp)
  (setq font-lock-keywords lego-font-lock-terms)
  (lego-init-syntax-table)
  (proof-goals-config-done))
  

(provide 'lego)
