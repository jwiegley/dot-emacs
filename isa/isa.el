;; isa-mode.el	 Emacs support for Isabelle proof assistant
;; Copyright (C) 1993-2000 LFCS Edinburgh, David Aspinall.
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;; Author:    David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; -----------------------------------------------------------------
;;
;; This file and the rest of Isabelle Proof General contain code taken
;; from David Aspinall's Isamode system, a personal project undertaken
;; 1993-1999 as a contribution to the Isabelle community.
;;
;; -----------------------------------------------------------------


;; Add Isabelle image onto splash screen
(setq proof-splash-extensions
      '(list
	nil
	(proof-get-image "isabelle_transparent" t)))

;; In case Isa mode was invoked directly or by -*- isa -*- at
;; the start of the file, ensure that Isa mode is used from now
;; on for .thy and .ML files.  
;; FIXME: be less messy with auto-mode-alist here (remove dups)
(setq auto-mode-alist 
      (cons '("\\.ML$\\|\\.thy$" . isa-mode) auto-mode-alist))

(require 'proof)
(require 'isa-syntax)
(require 'isabelle-system)

;;;
;;; ======== User settings for Isabelle ========
;;;

;;; proof-site provides us with the cusomization groups
;;;
;;; 'isabelle         -  User options for Isabelle Proof General
;;; 'isabelle-config  -  Configuration of Isabelle Proof General
;;;			 (constants, but may be nice to tweak)


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
   proof-script-comment-start		"(*"	; comment in a proof
   proof-script-comment-end		"*)"	; 
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

   proof-indent-enclose-offset  (- proof-indent)
   proof-indent-open-offset     0
   proof-indent-close-offset    0
   proof-indent-any-regexp      isa-indent-any-regexp
   proof-indent-inner-regexp    isa-indent-inner-regexp
   proof-indent-enclose-regexp  isa-indent-enclose-regexp
   proof-indent-open-regexp     isa-indent-open-regexp
   proof-indent-close-regexp    isa-indent-close-regexp
   
   ;; proof engine commands
   proof-showproof-command	"pr();"
   proof-goal-command		"Goal \"%s\";"
   proof-save-command		"qed \"%s\";"
   proof-context-command	"ProofGeneral.show_context();"
   proof-info-command		"ProofGeneral.help();"
   proof-kill-goal-command	"ProofGeneral.kill_goal();"
   proof-find-theorems-command  "ProofGeneral.thms_containing (space_explode \",\" \"%s\");"
   proof-shell-start-silent-cmd "Goals.disable_pr();"
   proof-shell-stop-silent-cmd  "Goals.enable_pr();"
   ;; command hooks
   proof-goal-command-p		'isa-goal-command-p
   proof-count-undos-fn		'isa-count-undos
   proof-find-and-forget-fn	'isa-find-and-forget
   proof-state-preserving-p	'isa-state-preserving-p

   ;; close goal..save regions eagerly
   proof-completed-proof-behaviour 'closeany

   proof-shell-compute-new-files-list 'isa-shell-compute-new-files-list
   proof-shell-inform-file-processed-cmd 
   "ProofGeneral.inform_file_processed \"%s\";"
   proof-shell-inform-file-retracted-cmd 
   "ProofGeneral.inform_file_retracted \"%s\";"

   ;; Parsing error messages.  Bit tricky to allow for
   ;; multitude of possible error formats Isabelle spits out.
   ;; Ideally we shouldn't bother parsing errors that appear
   ;; in the temporary ML files generated while reading
   ;; theories, but unfortunately the user sometimes needs to 
   ;; examine them to understand a strange problem...
   proof-shell-next-error-regexp
   "\\(error on \\|Error: in '[^']+', \\)line \\([0-9]+\\)\\|The error(s) above occurred"
   proof-shell-next-error-filename-regexp
   "\\(Loading theory \"\\|Error: in '\\)\\([^\"']+\\)[\"']"
   proof-shell-next-error-extract-filename
   "%s.thy"))

  


(defun isa-shell-mode-config-set-variables ()
  "Configure generic proof shell mode variables for Isabelle."
  (setq
   pg-subterm-first-special-char	?\350

   proof-shell-wakeup-char		 ?\372
   proof-shell-annotated-prompt-regexp   "\\(val it = () : unit\n\\)?> \372"

   ;; This pattern is just for comint
   proof-shell-prompt-pattern		"^2?[ML-=#>]>? \372?"

   ;; for issuing command, not used to track cwd in any way.
   proof-shell-cd-cmd			"ThyLoad.add_path \"%s\";"

   ;; Escapes for filenames inside ML strings.
   ;; We also make a hack for Isabelle, by switching from backslashes
   ;; to forward slashes if it looks like we're running on Windows.
   proof-shell-filename-escapes		
   (if (fboundp 'win32-long-file-name)	; rough test for XEmacs on win32 
       ;; Patterns to unixfy names.  Avoids a deliberate bomb in Isabelle which
       ;; barfs at paths with these characters in them.
       '(("\\\\" . "/") ("\"" . "\\\"") ("^[a-zA-Z]:" . ""))
     ;; Normal case: quotation for backslash, quote mark.
     '(("\\\\" . "\\\\") ("\""   . "\\\"")))

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
   pg-topterm-char	        ?\370

   proof-shell-proof-completed-regexp	"^No subgoals!"

   ;; initial command configures Isabelle by hacking print functions,
   ;; restoring settings saved by Proof General, etc.

   ;; FIXME: temporary hack for almost enabling/disabling printing.
   ;; Also for setting default values.
   proof-shell-pre-sync-init-cmd	"ProofGeneral.init false;"
   proof-shell-init-cmd		        (proof-assistant-settings-cmd)

   proof-shell-restart-cmd		"ProofGeneral.isa_restart();"
   proof-shell-quit-cmd			"quit();"

   ;; NB: the settings below will only recognize tracing output in
   ;; Isabelle 2001.
   proof-shell-eager-annotation-start   "\360\\|\362"
   proof-shell-eager-annotation-start-length 1
   proof-shell-eager-annotation-end     "\361\\|\363"
   ;; see isa-pre-shell-start for proof-shell-trace-output-regexp

   ;; Some messages delimited by eager annotations
   proof-shell-clear-response-regexp    "Proof General, please clear the response buffer."
   proof-shell-clear-goals-regexp       "Proof General, please clear the goals buffer."
   proof-shell-set-elisp-variable-regexp "Proof General, please set the variable \\([^ ]+\\) to: #\\([^#]+\\)#\\."
   proof-shell-theorem-dependency-list-regexp    "Proof General, the theorem dependencies are: \"\\([^\"]*\\)\"" 
   
   ;; Dirty hack to allow font-locking for output based on hidden
   ;; annotations, see isa-output-font-lock-keywords-1
   pg-use-specials-for-fontify t

   ;; === ANNOTATIONS  === ones here are broken
   proof-shell-result-start	        "\372 Pbp result \373"
   proof-shell-result-end		"\372 End Pbp result \373"
   pg-subterm-anns-use-stack		t
   pg-subterm-start-char		?\372
   pg-subterm-sep-char			?\373
   pg-subterm-end-char			?\374
   pg-after-fontify-output-hook		'isabelle-convert-idmarkup-to-subterm
					;'pg-remove-specials
   ;; FIXME: next one doesn't do quite the right thing, always returns 'a?
   pg-subterm-help-cmd			"printyp (type_of (read \"%s\"))"

   ;; === MULTIPLE FILE HANDLING ===
   proof-shell-process-file 
   (cons
    ;; Theory loader output and verbose update() output.
    "Proof General, this file is loaded: \"\\(.*\\)\""
    (lambda (str)
      (match-string 1 str)))
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
  ;; First make sure we're in the right directory to take care of
  ;; relative "files" paths inside theory file.
  (proof-cd-sync)
  (proof-shell-invisible-command
   (proof-format-filename
    ;; %r parameter means relative (don't expand) path
    (format "ProofGeneral.%supdate_thy_only \"%%r\";" (if try "try_" ""))
    (file-name-nondirectory (file-name-sans-extension file)))
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
	(setq pg-response-erase-flag nil))))

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
(define-derived-mode isa-goals-mode proof-goals-mode
  "Isabelle goals" nil
  (isa-goals-mode-config)))

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
	 (proof-string-match "\\.thy$" (buffer-file-name)))

    ;; Enter theory mode, but first configure settings for proof
    ;; script if they haven't been done already.  This is a hack,
    ;; needed because Proof General assumes that the script mode must
    ;; have been configured before shell mode can be triggered, which
    ;; isn't true for Isabelle.  
    ;; (proof-config-done-related and proof-shell-mode refer to
    ;; the troublesome settings in question)
    ;; 3.3 fix: add require proof-script since context menus are 
    ;; now added for response/goals buffer, which requires proof mode. 
    (unless proof-terminal-char
      (require 'proof-script)
      (proof-menu-define-specific)	
      (isa-mode-config-set-variables)
      )

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

(defcustom isa-retract-thy-file-command "ThyInfo.remove_thy \"%r\";"
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
  (proof-ids-to-regexp '("undo"))
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
;;   Isa shell startup and exit hooks                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isa-pre-shell-start ()
  (setq proof-prog-name		(isabelle-command-line))
  (setq proof-mode-for-shell    'isa-shell-mode)
  (setq proof-mode-for-goals	'isa-goals-mode)
  (setq proof-mode-for-response 'isa-response-mode)
  (setq proof-shell-trace-output-regexp "\375"))

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


;; These hooks are added on load because proof shells can
;; be started from .thy (not in scripting mode) or .ML files.
;; 3.4: pre-shell-start-hook was a local hook, but then caused
;; new probs in E21 with not setting in correct buffer for shell(?)
(add-hook 'proof-pre-shell-start-hook 'isa-pre-shell-start); nil t
(add-hook 'proof-shell-insert-hook 'isa-preprocessing)

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

(defun isa-goals-mode-config ()
  ;; FIXME: next two broken, of course, as is PBP everywhere except LEGO.
  (setq pg-goals-change-goal "Show %s.")	
  (setq pg-goals-error-regexp proof-shell-error-regexp)
  (isa-init-output-syntax-table)
  (setq font-lock-keywords isa-goals-font-lock-keywords)
  (proof-goals-config-done))

(defun isa-preprocessing ()  ;dynamic scoping of `string'
  "Handle ^VERBATIM marker -- acts on variable STRING by dynamic scoping"
  (if (proof-string-match isabelle-verbatim-regexp string)
      (setq string (match-string 1 string))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; x-symbol support for Isabelle PG, provided by David von Oheimb.
;;
;; The following settings configure the generic PG package.
;; The token language "Isabelle Symbols" is in file x-symbol-isabelle.el
;;

(setq proof-xsym-extra-modes '(thy-mode)
      proof-xsym-activate-command
      "print_mode := ([\"xsymbols\",\"symbols\"] @ ! print_mode);"
      proof-xsym-deactivate-command
      "print_mode := (! print_mode \\\\ [\"xsymbols\",\"symbols\"]);")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Completion table for Isabelle identifiers
;;
;; Ideally this could be set automatically from the running process,
;; and maybe a default value could be dumped by Isabelle when it is
;; built.

(defpgdefault completion-table
  '("quit" 
    "cd" "use" "use_thy" "time_use" "time_use_thy"
    "Pretty.setdepth" "Pretty.setmargin" "print_depth"
    "show_hyps" "show_types" "show_sorts"
    "print_exn"
    "goal" "goalw" "goalw_cterm" "premises"
    "by" "byev" 
    "result" "uresult"
    "chop" "choplev" "back" "undo"
    "pr" "prlev" "goals_limit"
    "proof_timing"
    "prove_goal" "prove_goalw" "prove_goalw_cterm"
    "push_proof" "pop_proof" "rotate_proof"
    "save_proof" "restore_proof"
    "read" "prin" "printyp"
    "topthm" "getgoal" "gethyps"
    "filter_goal" "compat_goal"

    ;; short cuts - should these be included?
    "ba" "br" "be" "bd" "brs" "bes" "bds"
    "fs" "fr" "fe" "fd" "frs" "fes" "fds"
    "bw" "bws" "ren"

    "resolve_tac" "eresolve_tac" "dresolve_tac" "forward_tac"
    "assume_tac" "eq_assume_tac"
    "match_tac" "ematch_tac" "dmatch_tac"
    "res_inst_tac" "eres_inst_tac" "dres_inst_tac" "forw_inst_tac"
    "rewrite_goals_tac" "rewrite_tac" "fold_goals_tac"
    "fold_goals_tac" "fold_tac"
    "cut_facts_tac" "subgoal_tac"

    ;; short cuts - should these be included?
    "rtac" "etac" "dtac" "atac" "ares_tac" "rewtac"

    ;; In general, I think rules should appear in rule tables, not here.
    "asm_rl" "cut_rl"  

    "flexflex_tac" "rename_tac" "rename_last_tac"
    "Logic.set_rename_prefix" "Logic.auto_rename"

    "compose_tac"

    "biresolve_tac" "bimatch_tac" "subgoals_of_brl" "lessb"
    "head_string" "insert_thm" "delete_thm" "compat_resolve_tac"

    "could_unify" "filter_thms" "filt_resolve_tac"

    ;; probably shouldn't be included:
    "tapply" "Tactic" "PRIMITIVE" "STATE" "SUBGOAL"

    "pause_tac" "print_tac"

    "THEN" "ORELSE" "APPEND" "INTLEAVE"
    "EVERY" "FIRST" "TRY" "REPEAT_DETERM" "REPEAT" "REPEAT1"
    "trace_REPEAT"
    "all_tac" "no_tac"
    "FILTER" "CHANGED" "DEPTH_FIRST" "DEPTH_SOLVE"
    "DEPTH_SOLVE_1" "trace_DEPTH_FIRST"
    "BREADTH_FIRST" "BEST_FIRST" "THEN_BEST_FIRST"
    "trace_BEST_FIRST"
    "COND" "IF_UNSOLVED" "DETERM" 
    
    "SELECT_GOAL" "METAHYPS"

    "ALLGOALS" "TRYALL" "SOMEGOAL" "FIRSTGOAL"
    "REPEAT_SOME" "REPEAT_FIRST" "trace_goalno_tac"

    ;; include primed versions of tacticals?

    "EVERY1" "FIRST1"

    "prth" "prths" "prthq"
    "RSN" "RLN" "RL"

    ;; simplifier
    
    "addsimps" "addeqcongs" "delsimps"
    "setsolver" "setloop" "setmksimps" "setsubgoaler"
    "empty_ss" "merge_ss" "prems_of_ss" "rep_ss"
    "simp_tac" "asm_full_simp_tac" "asm_simp_tac"

    ;; classical prover

    "empty_cs" 
    "addDs" "addEs" "addIs" "addSDs" "addSEs" "addSIs" 
    "print_cs" 
    "rep_claset" "best_tac" "chain_tac" "contr_tac" "eq_mp_tac"
    "fast_tac" "joinrules" "mp_tac" "safe_tac" "safe_step_tac" 
    "slow_best_tac" "slow_tac" "step_tac" "swapify" 
    "swap_res_tac" "inst_step_tac" 
    
    ;; that's it for now!
    ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Theorem dependencies  (experimental)
;;

(defpacustom theorem-dependencies nil
  "Whether to track theorem dependencies within Proof General."
  :type 'boolean
  ;; when this is built-in  (or with a ":=%b" setting).
  ;; :setting ("depends_enable()" . "depends_disable()")
  :eval (isa-theorem-dependencies-switch))

(defvar isa-dependsml-file-loaded nil)

(add-hook 'proof-shell-kill-function-hooks
	  (lambda () (setq isa-dependsml-file-loaded nil)))

(defun isa-load-dependsml-file ()
  ;; NB: maybe doesn't work if enabled before Isabelle starts.
  (if (proof-shell-available-p)
      (progn
	(proof-shell-invisible-command
	 (proof-format-filename
	  "use \"%r\";"
	  (concat (file-name-directory 
		   (locate-library "isa"))
		  "depends.ML")))
	(setq isa-dependsml-file-loaded t))))

(defun isa-theorem-dependencies-switch ()
  "Switch on/off theorem dependency tracking.  (Experimental feature)."
  (if (and isa-theorem-dependencies (not isa-dependsml-file-loaded))
      (isa-load-dependsml-file))
  (proof-shell-invisible-command (if isa-theorem-dependencies
				     "depends_enable()"
				   "depends_disable()")))
  
  



(provide 'isa)
