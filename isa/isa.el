;; isa.el Major mode for Isabelle proof assistant
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>

;;
;; $Id$
;;


;; Add Isabelle image onto splash screen
;;
(customize-set-variable
 'proof-splash-extensions
 '(list
   nil
   (proof-splash-display-image "isabelle_transparent" t)))

(require 'proof)
(require 'isa-syntax)

;;;
;;; ======== User settings for Isabelle ========
;;;

;;; proof-site provides us with the cusomization groups
;;;
;;; 'isabelle         -  User options for Isabelle Proof General
;;; 'isabelle-config  -  Configuration of Isabelle Proof General
;;;			 (constants, but may be nice to tweak)

; FIXME: fancy logic choice stuff to go in for 3.2
;(defcustom isabelle-logic "HOL"
;  "*Choice of logic to use with Isabelle.
;If non-nil, will be added into isabelle-prog-name as default value."
;  :type (append
;	 (list 'choice '(const :tag "Unset" nil))
;	 (mapcar (lambda (str) (list 'const str))
;		 (split-string-by-char
;		  (substring (shell-command-to-string "isatool findlogics") 0 -1)
;		  ?\ )))
;  :group 'isabelle)

(defcustom isabelle-prog-name 
  (if (fboundp 'win32-long-filename)	; rough test for XEmacs on win32
      "C:\\sml\\bin\\.run\\run.x86-win32.exe @SMLload=C:\\Isabelle\\HOL"
    "isabelle")
  "*Name of program to run Isabelle.
The default value when running under Windows expects SML/NJ in C:\\sml
and an Isabelle image for HOL in C:\Isabelle.  You can change this
by customization."
  :type 'file
  :group 'isabelle)

(defcustom isabelle-indent 2
  "*Indentation degree in proof scripts.
Somewhat irrelevant for Isabelle because normal proof scripts have
no regular or easily discernable structure."
  :type 'number
  :group 'isabelle)

(defcustom isabelle-web-page
  "http://www.cl.cam.ac.uk/Research/HVG/Isabelle/"
  ;; "http://www.dcs.ed.ac.uk/home/isabelle"
  "URL of web page for Isabelle."
  :type 'string
  :group 'isabelle)

;;;
;;; ======== Configuration of generic modes ========
;;;

(defcustom isa-outline-regexp
  (proof-ids-to-regexp '("goal" "Goal" "prove_goal"))
  "Outline regexp for Isabelle ML files"
  :type 'regexp
  :group 'isabelle-config)

;;; End of a command needs parsing to find, so this is approximate.
(defcustom isa-outline-heading-end-regexp ";[ \t\n]*"
  "Outline heading end regexp for Isabelle ML files."
  :type 'regexp
  :group 'isabelle-config)

(defvar isa-shell-outline-regexp "\370[ \t]*\\([0-9]+\\)\\.")
(defvar isa-shell-outline-heading-end-regexp "$")




(defun isa-mode-config-set-variables ()
  "Configure generic proof scripting/thy mode variables for Isabelle.
Settings here are the ones which are needed for both shell mode
and script mode."
  (setq
   proof-assistant-home-page	isabelle-web-page
   proof-mode-for-script	'isa-proofscript-mode
   ;; proof script syntax
   proof-terminal-char		?\;	; ends a proof
   proof-comment-start		"(*"	; comment in a proof
   proof-comment-end		"*)"	; 
   ;; Next few used for func-menu and recognizing goal..save regions in
   ;; script buffer.
   proof-save-command-regexp    isa-save-command-regexp
   proof-goal-command-regexp    isa-goal-command-regexp
   proof-goal-with-hole-regexp  isa-goal-with-hole-regexp 
   proof-save-with-hole-regexp  isa-save-with-hole-regexp
   ;; Unfortunately the default value of proof-script-next-entity-regexps
   ;; is no good, because goals with holes in Isabelle are batch
   ;; commands, and not terminated by saves.  So we omit the forward
   ;; search from the default value.
   proof-script-next-entity-regexps
   (list (proof-regexp-alt
	  isa-goal-with-hole-regexp
	  isa-save-with-hole-regexp)
	 (list isa-goal-with-hole-regexp 2)
	 (list isa-save-with-hole-regexp 2
	       'backward isa-goal-command-regexp))
   ;;
   proof-indent-commands-regexp	(proof-ids-to-regexp isa-keywords)
   
   ;; proof engine commands
   proof-showproof-command	"pr()"
   proof-goal-command		"Goal \"%s\";"
   proof-save-command		"qed \"%s\";"
   proof-context-command	"ProofGeneral.show_context()"
   proof-info-command		"ProofGeneral.help()"
   proof-kill-goal-command	"ProofGeneral.kill_goal();"
   proof-find-theorems-command  "ProofGeneral.thms_containing [\"%s\"]"
   proof-shell-start-silent-cmd "proofgeneral_disable_pr();"
   proof-shell-stop-silent-cmd  "proofgeneral_enable_pr();"   
   ;; command hooks
   proof-goal-command-p		'isa-goal-command-p
   proof-count-undos-fn		'isa-count-undos
   proof-find-and-forget-fn	'isa-find-and-forget
   proof-state-preserving-p	'isa-state-preserving-p
   proof-parse-indent		'isa-parse-indent
   proof-stack-to-indent	'isa-stack-to-indent

   ;; close goal..save regions eagerly
   proof-completed-proof-behaviour 'closeany

   proof-shell-compute-new-files-list 'isa-shell-compute-new-files-list
   proof-shell-inform-file-processed-cmd 
   "ProofGeneral.inform_file_processed \"%s\";"
   proof-shell-inform-file-retracted-cmd 
   "ProofGeneral.inform_file_retracted \"%s\";"))


(defun isa-shell-mode-config-set-variables ()
  "Configure generic proof shell mode variables for Isabelle."
  (setq
   proof-shell-first-special-char	?\350

   proof-shell-wakeup-char		 ?\372
   proof-shell-annotated-prompt-regexp   "\\(val it = () : unit\n\\)?> \372"

   ;; This pattern is just for comint
   proof-shell-prompt-pattern		"^2?[ML-=#>]>? \372?"

   ;; for issuing command, not used to track cwd in any way.
   proof-shell-cd-cmd			"Library.cd \"%s\""

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


   ;; FIXME: the next two are probably only good for NJ/SML
   proof-shell-interrupt-regexp         "Interrupt"
   proof-shell-error-regexp		"^\364\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception-\\( \\|$\\)"
   
   ;; matches names of assumptions
   proof-shell-assumption-regexp	isa-id
   ;; matches subgoal name
   ;; FIXME: not used yet.  In future will be used for
   ;; proof-by-pointing like features.
   ;; proof-shell-goal-regexp		"\370[ \t]*\\([0-9]+\\)\\."

   proof-shell-start-goals-regexp	"\366"
   proof-shell-end-goals-regexp		"\367"
   proof-shell-goal-char	        ?\370

   ;; FIXME da: this needs improvement.  I don't know why just
   ;; "No subgoals!" isn't enough.  (Maybe anchored to end-goals
   ;; for safety).  At the moment, this regexp reportedly causes
   ;; overflows with large proof states. 
   proof-shell-proof-completed-regexp
   (concat proof-shell-start-goals-regexp
	   "\\(\\(.\\|\n\\)*\nNo subgoals!\n\\)"
	   proof-shell-end-goals-regexp)

   ;; initial command configures Isabelle by hacking print functions.
   ;; FIXME: temporary hack for almost enabling/disabling printing.
   proof-shell-init-cmd                 "val pg_saved_gl = ref (!goals_limit); fun proofgeneral_enable_pr () = goals_limit:= !pg_saved_gl; fun proofgeneral_disable_pr() = (pg_saved_gl := !goals_limit; goals_limit := 0); ProofGeneral.init false;"
   proof-shell-restart-cmd		"ProofGeneral.isa_restart();"
   proof-shell-quit-cmd			"quit();"
   
   proof-shell-eager-annotation-start   "\360\\|\362"
   proof-shell-eager-annotation-start-length 1
   proof-shell-eager-annotation-end     "\361\\|\363"

   ;; Some messages delimited by eager annotations
   proof-shell-clear-response-regexp    "Proof General, please clear the response buffer."
   proof-shell-clear-goals-regexp       "Proof General, please clear the goals buffer."

   ;; Dirty hack to allow font-locking for output based on hidden
   ;; annotations, see isa-output-font-lock-keywords-1
   proof-shell-leave-annotations-in-output t

   proof-goals-display-qed-message	t

   ;; === ANNOTATIONS  === ones here are broken
   proof-shell-result-start	        "\372 Pbp result \373"
   proof-shell-result-end		"\372 End Pbp result \373"
   proof-analyse-using-stack		t
   proof-shell-start-char		?\372
   proof-shell-end-char			?\373
   proof-shell-field-char		?\374

   ;; === MULTIPLE FILE HANDLING ===
   proof-shell-process-file 
   (cons
    ;; Theory loader output and verbose update() output.
    "Proof General, this file is loaded: \"\\(.*\\)\""
    (lambda (str)
      (match-string 1 str)))
   ;; \\|Not reading \"\\(.*\\)\"
   ;;    (lambda (str)
   ;;   (or (match-string 1 str) 
   ;;	  (match-string 2 str))))
   ;; This is the output returned by a special command to
   ;; query Isabelle for outdated files.
 ;;   proof-shell-clear-included-files-regexp
 ;;   "Proof General, please clear your record of loaded files."
   proof-shell-retract-files-regexp
   "Proof General, you can unlock the file \"\\(.*\\)\""
   proof-shell-compute-new-files-list 'isa-shell-compute-new-files-list
   )
  (add-hook 'proof-activate-scripting-hook 'isa-shell-update-thy 'append)
  )


;;;
;;; Theory loader operations
;;;

;; Experiments for background non-blocking loading of theory: this is
;; quite difficult, actually: we need to set a callback from
;; proof-done-invisible to take the final step in switching on
;; scripting.  We may be able to pass the hook argument into the
;; action list using the "span" argument which means nothing for
;; invisible command usually.

; attempt to trap C-g.  Needs more work so revert to previous
;(defun isa-update-thy-only (file try wait)
;  "Tell Isabelle to update current buffer's theory, and all ancestors."
;  ;; Trap interrupts from C-g during the update
;  (condition-case err
;      (proof-shell-invisible-command
;       (format "ProofGeneral.%supdate_thy_only \"%s\";"
;	       (if try "try_" "") (file-name-sans-extension file))
;       wait)
;    (t (message "Isabelle Proof General: error or interrupt during update theory...")
;       (if proof-shell-busy
;	   (proof-interrupt-process))
;       (sit-for 1)
;       (proof-deactivate-scripting)
;       (if (cdr err) ;; quit is just (quit).  
;	   (error (cdr err))))))

(defun isa-update-thy-only (file try wait)
  "Tell Isabelle to update current buffer's theory, and all ancestors."
  (proof-shell-invisible-command
   (proof-format-filename
    (format "ProofGeneral.%supdate_thy_only \"%%s\";" (if try "try_" ""))
    (file-name-sans-extension file))
   wait))

(defun isa-shell-update-thy ()
  "Possibly issue update_thy_only command to Isabelle.
If the current buffer has an empty locked region, the interface is
about to send commands from it to Isabelle.  This function sends
a command to read any theory file corresponding to the current ML file.
This is a hook function for proof-activate-scripting-hook."
  (if (proof-locked-region-empty-p)
       ;; If we switch to this buffer and it *does* have a locked
       ;; region, we could check that no updates are needed and
       ;; unlock the whole buffer in case they were.  But that's
       ;; a bit messy.  Instead we assume that things must be
       ;; up to date, after all, the user wasn't allowed to edit
       ;; anything that this file depends on, was she?
      (progn
	;; Wait after sending, so that queue is cleared for further
	;; commands without giving "proof process busy" error.
	(isa-update-thy-only buffer-file-name t 
			     ;; whether to block or not
			     (if (and (boundp 'activated-interactively)
					activated-interactively)
				 t ; was nil, but falsely leaves Scripting on! 
			       t))
	;; Leave the messages from the update around.
	(setq proof-shell-erase-response-flag nil))))

(defun isa-remove-file (name files cmp-base)
  (if (not files) nil
    (let*
	((file (car files))
	 (rest (cdr files))
	 (same (if cmp-base (string= name (file-name-nondirectory file))
		 (string= name file))))
      (if same (isa-remove-file name rest cmp-base)
	(cons file (isa-remove-file name rest cmp-base))))))

(defun isa-shell-compute-new-files-list (str)
  "Compute the new list of files read by the proof assistant.
This is called when Proof General spots output matching
proof-shell-retract-files-regexp."
  (let*
      ((name (match-string 1 str))
       (base-name (file-name-nondirectory name)))
    (if (string= name base-name)
	(isa-remove-file name proof-included-files-list t)
      (isa-remove-file (file-truename name) proof-included-files-list nil))))


;;
;;   Define the derived modes 
;;
(eval-and-compile
(define-derived-mode isa-shell-mode proof-shell-mode
   "Isabelle shell" nil
   (isa-shell-mode-config)))

(eval-and-compile
(define-derived-mode isa-response-mode proof-response-mode
  "Isabelle response" nil
  (isa-response-mode-config)))

(eval-and-compile			; to define vars for byte comp.
(define-derived-mode isa-pbp-mode pbp-mode
  "Isabelle goals" nil
  (isa-pbp-mode-config)))

(eval-and-compile			; to define vars for byte comp.
(define-derived-mode isa-proofscript-mode proof-mode
    "Isabelle script" nil
    (isa-mode-config)))


;;
;; Automatically selecting theory mode or Proof General script mode.
;;

(defun isa-mode ()
  "Mode for Isabelle buffers: either isa-proofscript-mode or thy-mode.
Files with extension .thy will be in thy-mode, otherwise we choose
isa-proofscript-mode."
  (interactive)
  (cond
   (;; Theory files only if they have the right extension
    (and (buffer-file-name)
	 (string-match "\\.thy$" (buffer-file-name)))

    ;; Enter theory mode, but first configure settings for proof
    ;; script if they haven't been done already.  This is a hack,
    ;; needed because Proof General assumes that the script mode must
    ;; have been configured before shell mode can be triggered, which
    ;; isn't true for Isabelle.  
    ;; (proof-config-done-related and proof-shell-mode refer to
    ;; the troublesome settings in question)
    (unless proof-terminal-char
      (isa-mode-config-set-variables))

    (thy-mode)

    ;; related mode configuration including locking buffer,
    ;; fontification, etc.
    (proof-config-done-related)		

    ;; Hack for splash screen
    (if (and (boundp 'proof-mode-hook)
	     (memq 'proof-splash-timeout-waiter proof-mode-hook))
	(proof-splash-timeout-waiter)
      ;; Otherwise, user may need welcoming.
      (proof-splash-message)))
   (t 
    (isa-proofscript-mode))))

(eval-after-load 
 "thy-mode"
 ;; Extend theory mode keymap
 '(let ((map thy-mode-map))
(define-key map "\C-c\C-b" 'isa-process-thy-file)
(define-key map "\C-c\C-r" 'isa-retract-thy-file)
(proof-define-keys map proof-universal-keys)))

;; FIXME: could test that the buffer isn't already locked.
(defun isa-process-thy-file (file)
  "Process the theory file FILE.  If interactive, use buffer-file-name."
  (interactive (list buffer-file-name))
  (save-some-buffers)
  (isa-update-thy-only file nil nil))

(defcustom isa-retract-thy-file-command "ThyInfo.remove_thy \"%s\";"
  "Sent to Isabelle to forget theory file and descendants.
Resulting output from Isabelle will be parsed by Proof General."
  :type 'string
  :group 'isabelle-config)

(defun isa-retract-thy-file (file)
  "Retract the theory file FILE. If interactive, use buffer-file-name.
To prevent inconsistencies, scripting is deactivated before doing this. 
So if scripting is active in an ML file which is not completely processed, 
you will be asked to retract the file or process the remainder of it."
  (interactive (list buffer-file-name))
  (proof-deactivate-scripting)
  (proof-shell-invisible-command
   (proof-format-filename isa-retract-thy-file-command
			  (file-name-nondirectory 
			   (file-name-sans-extension file)))))


;; Next bits taken from isa-load.el
;; isa-load.el,v 3.8 1998/09/01 

(defgroup thy nil
  "Customization of Isamode's theory editing mode"
  ;; :link '(info-link "(Isamode)Theory Files")
  :load 'thy-mode
  :group 'isabelle)

(autoload 'thy-mode "thy-mode" 
	  "Major mode for Isabelle theory files" t nil)

(autoload 'thy-find-other-file "thy-mode" 
	    "Find associated .ML or .thy file." t nil)

(defun isa-splice-separator (sep strings)
  (let (stringsep)
    (while strings
      (setq stringsep (concat stringsep (car strings)))
      (setq strings (cdr strings))
      (if strings (setq stringsep 
			(concat stringsep sep))))
    stringsep))

(defun isa-file-name-cons-extension (name)
  "Return cons cell of NAME without final extension and extension"
  (if (string-match "\\.[^\\.]+$" name)
      (cons (substring name 0 (match-beginning 0))
	    (substring name (match-beginning 0)))
    (cons name "")))

(defun isa-format (alist string)
  "Format a string by matching regexps in ALIST against STRING"
  (while alist
    (while (string-match (car (car alist)) string)
      (setq string
	    (concat (substring string 0 (match-beginning 0))
		    (cdr (car alist))
		    (substring string (match-end 0)))))
    (setq alist (cdr alist)))
  string)

;; Key to switch to theory mode
(define-key isa-proofscript-mode-map 
  [(control c) (control o)] 'thy-find-other-file)




;;
;;  Code that's Isabelle specific
;;

(defcustom isa-not-undoable-commands-regexp
  (proof-ids-to-regexp '("undo" "back"))
  "Regular expression matching commands which are *not* undoable."
  :type 'regexp
  :group 'isabelle-config)

;; This next function is the important one for undo operations.
(defun isa-count-undos (span)
  "Count number of undos in a span, return the command needed to undo that far."
  (let 
      ((case-fold-search nil)
       (ct 0) str i)
    (if (and span (prev-span span 'type)
	     (not (eq (span-property (prev-span span 'type) 'type) 'comment))
	     (isa-goal-command-p
	      (span-property (prev-span span 'type) 'cmd)))
	(concat "choplev 0" proof-terminal-string)
      (while span
	(setq str (span-property span 'cmd))
	(cond ((eq (span-property span 'type) 'vanilla)
	       (or (proof-string-match isa-not-undoable-commands-regexp str)
		   (setq ct (+ 1 ct))))
	      ((eq (span-property span 'type) 'pbp)
	       ;; this case probably redundant for Isabelle, unless we
	       ;; think of some nice ways of matching non-undoable cmds.
	       (cond ((not (proof-string-match 
			    isa-not-undoable-commands-regexp str))
		      (setq i 0)
		      (while (< i (length str))
			(if (= (aref str i) proof-terminal-char)
			    (setq ct (+ 1 ct)))
			(setq i (+ 1 i))))
		     (t nil))))
	(setq span (next-span span 'type)))
      (concat "ProofGeneral.repeat_undo " 
	      (int-to-string ct) proof-terminal-string))))

(defun isa-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (proof-string-match isa-goal-command-regexp str)) ; this regexp defined in isa-syntax.el

;; Isabelle has no concept of a Linear context, so forgetting back
;; to the declaration of a particular something makes no real
;; sense.  Perhaps in the future there will be functions to remove
;; theorems from theories, but even then all we could do is
;; forget particular theorems one by one.  So we ought to search
;; backwards in isa-find-and-forget, rather than forwards as
;; the code from the type theory provers does.

;; MMW: this version even does nothing at all
(defun isa-find-and-forget (span)
  proof-no-command)

(defun isa-state-preserving-p (cmd)
  "Non-nil if command preserves the proofstate."
  (not (proof-string-match isa-not-undoable-commands-regexp cmd)))

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
  (setq proof-mode-for-pbp	'isa-pbp-mode)
  (setq proof-mode-for-response 'isa-response-mode))

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
  (setq blink-matching-paren-dont-ignore-comments t))


;; This hook is added on load because proof shells can
;; be started from .thy (not in scripting mode) or .ML files.
(add-hook 'proof-pre-shell-start-hook 'isa-pre-shell-start nil t)

(defun isa-shell-mode-config ()
  "Configure Proof General proof shell for Isabelle."
  (isa-init-output-syntax-table)
  (setq font-lock-keywords isa-output-font-lock-keywords-1)
  (isa-shell-mode-config-set-variables)
  (proof-shell-config-done))

(defun isa-response-mode-config ()
  (setq font-lock-keywords isa-output-font-lock-keywords-1)
  (isa-init-output-syntax-table)
  (proof-response-config-done))

(defun isa-pbp-mode-config ()
  ;; FIXME: next two broken, of course, as is all PBP everywhere.
  (setq pbp-change-goal "Show %s.")	
  (setq pbp-error-regexp proof-shell-error-regexp)
  (isa-init-output-syntax-table)
  (setq font-lock-keywords isa-goals-font-lock-keywords)
  (proof-goals-config-done))


;; =================================================================
;;
;; x-symbol support for Isabelle PG, provided by David von Oheimb.
;;
;; The following settings configure the generic PG package.
;; The token language "Isabelle Symbols" is in file x-symbol-isa.el
;;

(setq proof-xsym-extra-modes '(thy-mode)
      proof-xsym-font-lock-keywords
      ;; fontification for tokens themselves  (FIXME: broken)
      '(("\\\\<[A-Za-z][A-Za-z0-9_']*>" (0 font-lock-type-face)))
      proof-xsym-activate-command
      "print_mode := (!print_mode union [\"xsymbols\",\"symbols\"])"
      proof-xsym-deactivate-command
      "print_mode := filter_out (fn x=>(rev (explode \"symbols\") prefix rev (explode x))) (!print_mode)")

(provide 'isa)
