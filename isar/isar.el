;; isar.el Major mode for Isabelle/Isar proof assistant
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Markus Wenzel <wenzelm@in.tum.de>
;;
;; $Id$
;;


;; Add Isabelle image onto splash screen
(customize-set-variable
 'proof-splash-extensions
 '(list
   nil
   (proof-splash-display-image "isabelle_transparent" t)))

;; In case Isar mode was invoked directly or by -*- isar -*- at
;; the start of the file, ensure that Isar mode is used from now
;; on for .thy files.
;; FIXME: be less messy with auto-mode-alist here (remove dups)
(setq auto-mode-alist 
      (cons '("\\.thy$" . isar-mode) auto-mode-alist))

(require 'proof)
(require 'isar-syntax)

;; Add generic code for Isabelle and Isabelle/Isar
(setq load-path (cons (concat proof-home-directory "isa/") load-path))
(require 'isabelle-system)


;; To make byte compiler be quiet.
;; NASTY: these result in loads when evaluated 
;; ordinarily (from non-byte compiled code).
;(eval-when-compile
;  (require 'proof-script)
;  (require 'proof-shell)
;  (require 'outline)
;  (cond ((fboundp 'make-extent) (require 'span-extent))
;	((fboundp 'make-overlay) (require 'span-overlay))))



;;; variable: proof-analyse-using-stack
;;;    proof-locked-region-empty-p, proof-shell-insert, proof-goals-mode,
;;;    proof-complete-buffer-atomic, proof-shell-invisible-command,
;;;    prev-span, span-property, next-span, proof-unprocessed-begin,
;;;    proof-config-done, proof-shell-config-done


;;;
;;; ======== User settings for Isabelle/Isar ========
;;;

;;; proof-site provides us with the cusomization groups
;;;
;;; 'isabelle-isar         -  User options for Isabelle/Isar Proof General
;;; 'isabelle-isar-config  -  Configuration of Isabelle/Isar Proof General
;;;	   		      (constants, but may be nice to tweak)

(defcustom isabelle-prog-name "isabelle"
  "*Name of program to run Isabelle/Isar."
  :type 'file
  :group 'isabelle-isar)

(defcustom isabelle-isar-indent 2
  "*Indentation degree in documents"
  :type 'number
  :group 'isabelle-isar)


;;;
;;; ======== Configuration of generic modes ========
;;;


;; ===== outline mode

(defcustom isar-outline-regexp
  (proof-ids-to-regexp isar-keywords-outline)
  "Outline regexp for Isabelle/Isar documents"
  :type 'regexp
  :group 'isabelle-isar-config)

;;; End of a command needs parsing to find, so this is approximate.
(defcustom isar-outline-heading-end-regexp ";[ \t\n]*"
  "Outline heading end regexp for Isabelle/Isar ML files."
  :type 'regexp
  :group 'isabelle-isar-config)

;; FIXME: not sure about this one
(defvar isar-shell-outline-regexp "\370[ \t]*\\([0-9]+\\)\\.")
(defvar isar-shell-outline-heading-end-regexp "$")

;(defun isar-outline-setup ()
;  (if (and window-system (string-match "XEmacs" emacs-version))
;      (progn
;	(custom-set-variables     ;custom value dictatorship!
;	 '(outline-mac-style t))
;	(outl-mouse-minor-mode))
;    (outline-minor-mode)))
;
; FIXME tmp
(defun isar-outline-setup () t)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Indentation                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isar-stack-to-indent (stack)
  (cond
   ((null stack) 0)
   ((null (car (car stack)))
    (nth 1 (car stack)))
   (t (let* ((col (save-excursion
		   (goto-char (nth 1 (car stack)))
		   (current-indentation)))
	    (ind-col (+ isabelle-isar-indent col)))
	(if (eq (car (car stack)) ?p)
	    (save-excursion
	      (move-to-column (current-indentation))
	      (cond
	       ((proof-looking-at isar-indent-enclose-regexp) col)
	       ((proof-looking-at isar-indent-reset-regexp) 0)
	       (t ind-col)))
	  ind-col)))))

(defun isar-parse-indent (c stack)
  (cond
   ;; toplevel / other
   ((proof-looking-at isar-indent-reset-regexp)
    (cons (list proof-terminal-char (point)) (list (list nil 0))))
   ((proof-looking-at isar-indent-regexp)
    (cons (list proof-terminal-char (point)) stack))
   ;; open / close
   ((proof-looking-at isar-indent-open-regexp)
    (cons (list ?p (point)) stack))
   ((and (proof-looking-at isar-indent-close-regexp)
	 (eq (car (car stack)) ?p))
    (cdr stack))
   (t stack)))


;;;
;;; theory header
;;;

(defun isar-detect-header ()
  "Detect new-style theory header in current buffer"
  (let ((header-regexp (proof-ids-to-regexp '("header" "theory")))
	(white-space-regexp "\\(\\s-\\|\n\\)+")
	(cmt-end-regexp (regexp-quote proof-comment-end))
	(cmt-start-regexp (regexp-quote proof-comment-start))
	(found-header nil) forward-amount
	(end (point-max)) (cont t) (cmt-level 0) c)
    (save-excursion
      (goto-char (point-min))
      (while (and cont (< (point) end))
	(setq c (char-after (point)))
	(setq forward-amount 1)
	(cond 
	 ;; comments
	 ((proof-looking-at cmt-start-regexp)
	  (setq forward-amount (length (match-string 0)))
	  (incf cmt-level))
	 ((proof-looking-at cmt-end-regexp)
	  (setq forward-amount (length (match-string 0)))
	  (decf cmt-level))
	 ((> cmt-level 0))
	 ;; white space
	 ((proof-looking-at white-space-regexp)
	  (setq forward-amount (length (match-string 0))))
	 ;; theory header
	 ((proof-looking-at header-regexp)
	  (setq found-header t)
	  (setq cont nil))
	 ;; bad stuff
	 (t
	  (setq cont nil)))
	(and cont (forward-char forward-amount)))
      found-header)))


;;; NB!  Disadvantage of *not* shadowing variables is that user
;;; cannot override them.  It might be nice to override some
;;; variables, which ones?

(defun isar-mode-config-set-variables ()
  "Configure generic proof scripting mode variables for Isabelle/Isar."
  (setq
   proof-assistant-home-page	isabelle-web-page
   proof-mode-for-script	'isar-proofscript-mode
   ;; proof script syntax
   proof-terminal-char		?\;	; ends a proof
   proof-comment-start		"(*"	; comment in a proof
   proof-comment-end		"*)"
   proof-string-start-regexp    "\"\\|{\\*"
   proof-string-end-regexp      "\"\\|\\*}"
   ;; Next few used for func-menu and recognizing goal..save regions in
   ;; script buffer.
   proof-save-command-regexp    isar-save-command-regexp
   proof-goal-command-regexp    isar-goal-command-regexp
   proof-goal-with-hole-regexp  isar-goal-with-hole-regexp
   proof-save-with-hole-regexp  isar-save-with-hole-regexp
   proof-indent-commands-regexp	"$^"
   ;; proof engine commands
   proof-showproof-command	"pr"
   proof-goal-command		"lemma \"%s\";"
   proof-save-command		"qed"
   proof-context-command	"print_context"
   proof-info-command		"help"
   proof-kill-goal-command	"ProofGeneral.kill_proof;"
   proof-find-theorems-command  "thms_containing %s;"
   proof-shell-start-silent-cmd "disable_pr;"
   proof-shell-stop-silent-cmd  "enable_pr;"   
   ;; command hooks
   proof-goal-command-p		'isar-goal-command-p
   proof-really-save-command-p	'isar-global-save-command-p
   proof-count-undos-fn		'isar-count-undos
   proof-find-and-forget-fn	'isar-find-and-forget
   ;; da: for pbp.  
   ;; proof-goal-hyp-fn		'isar-goal-hyp
   proof-state-preserving-p	'isar-state-preserving-p
   proof-script-indent          t
   proof-parse-indent		'isar-parse-indent
   proof-stack-to-indent	'isar-stack-to-indent
   proof-shell-compute-new-files-list 'isar-shell-compute-new-files-list))


(defun isar-shell-mode-config-set-variables ()
  "Configure generic proof shell mode variables for Isabelle/Isar."
  (setq
   proof-shell-first-special-char	?\350

   proof-shell-wakeup-char		?\372
   proof-shell-annotated-prompt-regexp  "^\\w*[>#] \372"

   ;; This pattern is just for comint.
   proof-shell-prompt-pattern		"^\\w*[>#] "

   ;; for issuing command, not used to track cwd in any way.
   proof-shell-cd-cmd			"ML {* Library.cd \"%s\" *}"

   ;; Escapes for filenames inside ML strings.
   ;; We also make a hack for a bug in Isabelle, by switching from 
   ;; backslashes to forward slashes if it looks like we're running
   ;; on Windows.
   proof-shell-filename-escapes		
   (if (fboundp 'win32-long-filename)	; rough test for XEmacs on win32 
       ;; Patterns to unixfy names.
       ;; Jacques Fleuriot's patch in ML does this too: ("^[a-zA-Z]:" . "") 
       ;; But I'll risk leaving drive names in, not sure how to replace them.
       '(("\\\\" . "/") ("\"" . "\\\""))
     ;; Normal case: quotation for backslash, quote mark.
     '(("\\\\" . "\\\\") ("\""   . "\\\"")))

   proof-shell-proof-completed-regexp   nil     ; n.a.
   proof-shell-interrupt-regexp         "\364\\*\\*\\* Interrupt\\|\360Interrupt"
   proof-shell-error-regexp		"^\364\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
   proof-shell-abort-goal-regexp        nil     ; n.a.

   ;; matches names of assumptions
   proof-shell-assumption-regexp	isar-id
   ;; matches subgoal name
   ;; da: not used at the moment, maybe after 3.0 used for
   ;; proof-generic-goal-hyp-fn to get pbp-like features.
   ;; proof-shell-goal-regexp		"\370[ \t]*\\([0-9]+\\)\\."

   proof-shell-start-goals-regexp	"\366\n"
   proof-shell-end-goals-regexp		"\367"
   proof-shell-goal-char	        ?\370

   ;; initial command configures Isabelle/Isar by modifying print
   ;; functions, restoring settings saved by Proof General, etc.
   proof-shell-init-cmd                 (concat
					 (isar-verbatim 
					  "ProofGeneral.init true;")
					 ;; FIXME: markus, could you sort this?
					 ;; Doesn't seem to work, maybe
					 ;; should be done later?  with verb?
					 ;; or before PG.init without m/u?
					 "\n"
					 (isabelle-set-default-cmd))
   proof-shell-restart-cmd		"ProofGeneral.restart;"
   proof-shell-quit-cmd			(isar-verbatim "quit();")
   
   proof-shell-eager-annotation-start-length 1
   proof-shell-eager-annotation-start   "\360\\|\362"
   proof-shell-eager-annotation-end     "\361\\|\363"

   ;; Some messages delimited by eager annotations
   proof-shell-clear-response-regexp    "Proof General, please clear the response buffer."
   proof-shell-clear-goals-regexp       "Proof General, please clear the goals buffer."

   ;; Tested values of proof-shell-eager-annotation-start: 
   ;; "^\\[opening \\|^###\\|^Reading\\|^Proof General\\|^Not reading"
   ;; "^---\\|^\\[opening "
   ;; could be last bracket on end of line, or with ### and ***.

   ;; Dirty hack to allow font-locking for output based on hidden
   ;; annotations, see isar-output-font-lock-keywords-1
   proof-shell-leave-annotations-in-output t

   ;; === ANNOTATIONS  === ones below here are broken
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
    "Proof General, this file is loaded: \"\\(.*\\)\""
    (lambda (str)
      (match-string 1 str)))
   proof-shell-retract-files-regexp
   "Proof General, you can unlock the file \"\\(.*\\)\""
   proof-shell-compute-new-files-list 'isar-shell-compute-new-files-list
   proof-shell-inform-file-processed-cmd "ProofGeneral.inform_file_processed \"%s\";"
   proof-shell-inform-file-retracted-cmd "ProofGeneral.inform_file_retracted \"%s\";")
  (add-hook 'proof-activate-scripting-hook 'isar-activate-scripting))


;;;
;;; Theory loader operations
;;;

(defun isar-remove-file (name files cmp-base)
  (if (not files) nil
    (let*
	((file (car files))
	 (rest (cdr files))
	 (same (if cmp-base (string= name (file-name-nondirectory file))
		 (string= name file))))
      (if same (isar-remove-file name rest cmp-base)
	(cons file (isar-remove-file name rest cmp-base))))))

(defun isar-shell-compute-new-files-list (str)
  "Compute the new list of files read by the proof assistant.
This is called when Proof General spots output matching
proof-shell-retract-files-regexp."
  (let*
      ((name (match-string 1 str))
       (base-name (file-name-nondirectory name)))
    (if (string= name base-name)
	(isar-remove-file name proof-included-files-list t)
      (isar-remove-file (file-truename name) proof-included-files-list nil))))

(defun isar-activate-scripting ()
  "Make sure the Isabelle/Isar toplevel is in a sane state.")
;FIXME  (proof-shell-invisible-command proof-shell-restart-cmd))


;;
;;   Define the derived modes 
;;
(eval-and-compile
(define-derived-mode isar-shell-mode proof-shell-mode
   "Isabelle/Isar shell" nil
   (isar-shell-mode-config)))

(eval-and-compile
(define-derived-mode isar-response-mode proof-response-mode
  "Isabelle/Isar response" nil
  (isar-response-mode-config)))

(eval-and-compile			; to define vars for byte comp.
(define-derived-mode isar-goals-mode proof-goals-mode
  "Isabelle/Isar proofstate" nil
  (isar-goals-mode-config)))

(eval-and-compile			; to define vars for byte comp.
(define-derived-mode isar-proofscript-mode proof-mode
    "Isabelle/Isar script" nil
    (isar-mode-config)))

(define-key isar-proofscript-mode-map
  [(control c) (control l)] 'proof-prf)	; keybinding like Isamode


(defun isar-mode ()
  "Mode for Isabelle/Isar interactive documents."
  (interactive)
  (cond
   (;; Hack for splash screen
    (if (and (boundp 'proof-mode-hook)
	     (memq 'proof-splash-timeout-waiter proof-mode-hook))
	(proof-splash-timeout-waiter))
    ;; Has this theory file already been loaded by Isabelle?
    ;; Colour it blue if so.  
    ;; NB: call to file-truename is needed for FSF Emacs which
    ;; chooses to make buffer-file-truename abbreviate-file-name
    ;; form of file-truename.
    (and (member (file-truename buffer-file-truename)
		 proof-included-files-list)
	 (proof-complete-buffer-atomic (current-buffer)))
    )
   (t 
    ;; Proof mode does that automatically.
    (isar-proofscript-mode))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's Isabelle/Isar specific                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; undo proof commands
(defun isar-count-undos (span)
  "Count number of undos in a span, return the command needed to undo that far."
  (let
      ((case-fold-search nil)
       (ct 0) str i)
    (while span
      (setq str (span-property span 'cmd))
      (cond ((eq (span-property span 'type) 'vanilla)
	     (or (proof-string-match isar-undo-skip-regexp str)
		 (setq ct (+ 1 ct))))
	    ((eq (span-property span 'type) 'pbp)
	     ;; this case probably redundant for Isabelle, unless
	     ;; we think of some nice ways of matching non-undoable
	     ;; commands.
	     (cond ((not (proof-string-match isar-undo-skip-regexp str))
		    (setq i 0)
		    (while (< i (length str))
		      (if (= (aref str i) proof-terminal-char)
			  (setq ct (+ 1 ct)))
		      (setq i (+ 1 i))))
		   (t nil))))
      (setq span (next-span span 'type)))
    (isar-undos ct)))

;; undo theory commands
(defun isar-find-and-forget (span)
  "Return commands to be used to forget SPAN."
  (let (str ans answers)
    (while span
      (setq str (span-property span 'cmd))
      (setq ans nil)
      (cond
       ;; comment or diagnostic command: skip
       ((or (eq (span-property span 'type) 'comment)
	    (proof-string-match isar-undo-skip-regexp str)))
       ;; finished goal: undo
       ((eq (span-property span 'type) 'goalsave)
	(setq ans isar-undo))
       ;; open goal: skip and exit
       ((proof-string-match isar-goal-command-regexp str)
	(setq span nil))
       ;; not undoable: fail and exit
       ((proof-string-match isar-undo-fail-regexp str)
	(setq answers nil)
	(setq ans (isar-cannot-undo str))
	(setq span nil))
       ;; theory: remove and exit
       ((proof-string-match isar-undo-remove-regexp str)
	(setq ans (isar-remove (match-string 2 str)))
	(setq span nil))
       ;; context switch: kill
       ((proof-string-match isar-undo-kill-regexp str)
	(setq ans isar-kill))
       ;; else: undo
       (t
	(setq ans isar-undo)))
      (if ans (setq answers (cons ans answers)))
      (if span (setq span (next-span span 'type))))
    (if (null answers) proof-no-command (apply 'concat answers))))



(defun isar-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (proof-string-match isar-goal-command-regexp str))

(defun isar-global-save-command-p (span str)
  "Decide whether argument really is a global save command"
  (or
   (string-match isar-global-save-command-regexp str)
   (let ((ans nil) (lev 0) cmd)
     (while (and span (not ans))
       (setq span (prev-span span 'type))
       (setq cmd (span-property span 'cmd))
       (cond
	;; comment: skip
	((eq (span-property span 'type) 'comment))
	;; local qed: enter block
	((proof-string-match isar-save-command-regexp cmd)
	 (setq lev (+ lev 1)))
	;; local goal: leave block, or done
	((proof-string-match isar-local-goal-command-regexp cmd)
	 (if (> lev 0) (setq lev (- lev 1)) (setq ans 'no)))
	;; global goal: done
	((proof-string-match isar-goal-command-regexp cmd)
	 (setq ans 'yes))))
     (eq ans 'yes))))

(defvar isar-current-goal 1
  "Last goal that emacs looked at.")

(defun isar-state-preserving-p (cmd)
  "Non-nil if command preserves the proofstate."
  (proof-string-match isar-undo-skip-regexp cmd))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Isar shell startup and exit hooks                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;borrowed from plastic.el
(defvar isar-shell-current-line-width nil
  "Current line width of the Isabelle process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;borrowed from plastic.el
(defun isar-shell-adjust-line-width ()
  "Use Isabelle's pretty printing facilities to adjust output line width.
   Checks the width in the `proof-goals-buffer'"
  (let ((ans ""))
    (and (buffer-live-p proof-goals-buffer)
	 (proof-shell-live-buffer)
	 (save-excursion
	   (set-buffer proof-goals-buffer)
	   (let ((current-width
		  ;; Actually, one might sometimes
		  ;; want to get the width of the proof-response-buffer
		  ;; instead. Never mind.
		  (max 20 (window-width (get-buffer-window proof-goals-buffer)))))
	     
	     (if (equal current-width isar-shell-current-line-width) ()
	       (setq isar-shell-current-line-width current-width)
	       (set-buffer proof-shell-buffer)
	       (setq ans (format "pretty_setmargin %d;" (- current-width 4)))))))
    ans))

(defun isar-pre-shell-start ()
  (setq proof-prog-name		isabelle-prog-name)
  (setq proof-mode-for-shell    'isar-shell-mode)
  (setq proof-mode-for-goals	'isar-goals-mode)
  (setq proof-mode-for-response 'isar-response-mode))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isar-preprocessing ()  ;dynamic scoping of `string'
  "Insert sync markers - acts on variable STRING by dynamic scoping"
  (if (string-match isar-verbatim-regexp string)
      (setq string (match-string 1 string))
    (setq string (concat "\\<^sync>" (isar-shell-adjust-line-width) string "\\<^sync>;"))))

(defun isar-mode-config ()
  (isar-mode-config-set-variables)
  (isar-init-syntax-table)
  (setq font-lock-keywords isar-font-lock-keywords-1)
  (proof-config-done)
  ;; outline
  ;; FIXME: do we need to call make-local-variable here?
  (make-local-variable 'outline-regexp)
  (setq outline-regexp isar-outline-regexp)
  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp isar-outline-heading-end-regexp)
  (isar-outline-setup)
  ;; tags
  ;  (and (boundp 'tag-table-alist)
  ;       (setq tag-table-alist
  ;	     (append '(("\\.ML$"  . isar-ML-file-tags-table)
  ;		       ("\\.thy$" . thy-file-tags-table))
  ;		     tag-table-alist)))
  (setq blink-matching-paren-dont-ignore-comments t)
  (add-hook 'proof-pre-shell-start-hook 'isar-pre-shell-start nil t)
  (add-hook 'proof-shell-insert-hook 'isar-preprocessing))


(defun isar-shell-mode-config ()
  "Configure Proof General proof shell for Isabelle/Isar."
  (isar-init-output-syntax-table)
  (setq font-lock-keywords isar-output-font-lock-keywords-1)
  (isar-shell-mode-config-set-variables)
  (proof-shell-config-done)
  (isar-outline-setup))

(defun isar-response-mode-config ()
  (setq font-lock-keywords isar-output-font-lock-keywords-1)
  (isar-init-output-syntax-table)
  (isar-outline-setup)
  (proof-response-config-done))

(defun isar-goals-mode-config ()
  ;; FIXME: next two broken, of course, as is PBP everywhere except LEGO.
  (setq pbp-change-goal "Show %s.")
  (setq pbp-error-regexp proof-shell-error-regexp)
  (isar-init-output-syntax-table)
  (setq font-lock-keywords isar-output-font-lock-keywords-1)
  (isar-outline-setup)
  (proof-goals-config-done))

;; =================================================================
;;
;; x-symbol support for Isabelle PG, provided by David von Oheimb.
;;
;; The following settings configure the generic PG package.
;; The token language "Isabelle Symbols" is in file x-symbol-isar.el
;;

(setq proof-xsym-font-lock-keywords
      '(("\\\\<[A-Za-z][A-Za-z0-9_']*>" (0 font-lock-type-face)))
      proof-xsym-activate-command
      "ML_command {* print_mode := ([\"xsymbols\",\"symbols\"] @ ! print_mode) *};"
      proof-xsym-deactivate-command
      "ML_command {* print_mode := (! print_mode \\\\ [\"xsymbols\",\"symbols\"]) *};")


(provide 'isar)
