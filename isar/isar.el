;; isar.el Major mode for Isabelle proof assistant
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Isabelle maintainer <isabelle@dcs.ed.ac.uk>

;;
;; isar.el,v 2.44 1998/11/10 18:08:50 da Exp
;;


;; FIXME: this most be done before loading proof-config, shame.
(setq proof-tags-support nil) ; no isatags prog, yet.

;; Add Isabelle image onto splash screen
(customize-set-variable
 'proof-splash-extensions
 '(list
   nil
   (proof-splash-display-image "isabelle_transparent" t)))

(require 'proof)
(require 'isar-syntax)

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
;;;    proof-locked-region-empty-p, proof-shell-insert, pbp-mode,
;;;    proof-mark-buffer-atomic, proof-shell-invisible-command,
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

(defcustom isabelle-isar-prog-name "isabelle"
  "*Name of program to run Isabelle/Isar."
  :type 'file
  :group 'isabelle-isar)

(defcustom isabelle-isar-indent 2
  "*Indentation degree in documents"
  :type 'number
  :group 'isabelle-isar)

(defcustom isabelle-web-page
  "http://isabelle.in.tum.de"
  "URL of web page for Isabelle."
  :type 'string
  :group 'isabelle-isar)

;;;
;;; ======== Configuration of generic modes ========
;;;

;; ===== outline mode

(defcustom isar-keywords-section
  '("chapter" "section" "subsection" "subsubsection" "text")
  "Isabelle/Isar section headings"
  :group 'isar-syntax
  :type '(repeat string))

(defcustom isar-outline-regexp
  (proof-ids-to-regexp (append isar-keywords-goal isar-keywords-section))
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

(defun isar-outline-setup ()
  (if (and window-system (string-match "XEmacs" emacs-version))
      (progn
	(custom-set-variables     ;custom value dictatorship!
	 '(outline-mac-style t))
	(outl-mouse-minor-mode))
    (outline-minor-mode)))

;;; ---- end-outline



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
   proof-comment-end		"*)"	; 
   ;; Next few used for func-menu and recognizing goal..save regions in
   ;; script buffer.
   proof-save-command-regexp    isar-save-command-regexp
   proof-goal-command-regexp    isar-goal-command-regexp
   proof-goal-with-hole-regexp  isar-goal-with-hole-regexp
   proof-save-with-hole-regexp  isar-save-with-hole-regexp
   proof-commands-regexp	(proof-ids-to-regexp isar-keywords)
   ;; proof engine commands (first three for menus, last for undo)
   proof-prf-string		"pr"
   proof-goal-command		"lemma \"%s\""
   proof-save-command		"qed"
   proof-ctxt-string		"print_theory"
   proof-help-string		"help"
   proof-kill-goal-command	"kill"
   ;; command hooks
   proof-goal-command-p		'isar-goal-command-p
   proof-count-undos-fn		'isar-count-undos
   proof-find-and-forget-fn	'isar-find-and-forget
   proof-goal-hyp-fn		'isar-goal-hyp
   proof-state-preserving-p	'isar-state-preserving-p
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
   proof-shell-cd			"cd \"%s\";"
   proof-shell-proof-completed-regexp   "FIXME No subgoals!"

   proof-shell-error-regexp		"^\364\\*\\*\\*"
   proof-shell-interrupt-regexp         "^Interrupt"
   
   ;; nothing appropriate for: proof-shell-abort-goal-regexp         ;; MMW FIXME: ??

   ;; matches names of assumptions
   proof-shell-assumption-regexp	isar-id
   ;; matches subgoal name
   ;; FIXME: proof-shell-goal-regexp is *not* used at the generic level!
   ;;        Perhaps it should be renamed to isar-goal-regexp and be
   ;;        set somewhere else.  
   proof-shell-goal-regexp		"\370[ \t]*\\([0-9]+\\)\\."

   proof-shell-start-goals-regexp	"\366"
   proof-shell-end-goals-regexp		"\367"
   proof-shell-goal-char	        ?\370
   ;; initial command configures Isabelle/Isar by hacking print functions.
   proof-shell-init-cmd
    (concat "use \"" proof-home-directory "isar/ProofGeneral.ML\";")
   proof-shell-restart-cmd		"restart;"
   proof-shell-quit-cmd			"quit;"
   
   proof-shell-eager-annotation-start   "\360\\|\362"
   proof-shell-eager-annotation-end     "\361\\|\363"

   ;; Some messages delimited by eager annotations
   proof-shell-clear-response-regexp    "Proof General, please clear the response buffer."
   proof-shell-clear-goals-regexp       "Proof General, please clear the goals buffer."

   ;; Tested values of proof-shell-eager-annotation-start: 
   ;; "^\\[opening \\|^###\\|^Reading\\|^Proof General\\|^Not reading"
   ;; "^---\\|^\\[opening "
   ;; could be last bracket on end of line, or with ### and ***.

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
   proof-shell-compute-new-files-list 'isar-shell-compute-new-files-list
   )
  (add-hook 'proof-activate-scripting-hook 'isar-shell-hack-use-thy)
  )


;;;
;;;  use_thy and friends.
;;;
;;; Quite tricky to get these right.  By default, Isabelle's
;;; theory loader glues together theory and ML files whenever
;;; it can, but that's not what we want here.
;;;
;;; So we rely on some hacked versions.
;;;

(defcustom isar-usethy-notopml-command "" ;;; FIXME "ProofGeneral.use_thy \"%s\";"
  "Sent to Isabelle/Isar to process theory for this ML file, and all ancestors."
  :type 'string
  :group 'isabelle-isar-config)

(defun isar-shell-hack-use-thy ()
  "Possibly issue  use_thy_no_topml command to Isabelle/Isar.
If the current buffer has an empty locked region, the interface is
about to send commands from it to Isabelle/Isar.  This function sends
a command to read any theory file corresponding to the current ML file.
This is a hook function for proof-activate-scripting-hook."
  (if (and
       (proof-locked-region-empty-p)
       ;; If we switch to this buffer and it *does* have a locked
       ;; region, we could check that no updates are needed and
       ;; unlock the whole buffer in case they were.  But that's
       ;; a bit messy.  Instead we assume that things must be
       ;; up to date, after all, the user wasn't allowed to edit
       ;; anything that this file depends on, was she?
       buffer-file-name
       (file-exists-p 
	(concat (file-name-sans-extension buffer-file-name) ".thy")))
      ;; Send a use_thy command if there is a corresponding .thy file.
      ;; Let Isabelle do the work of checking whether any work needs
      ;; doing.  Really this should be force_use_thy, too.
      ;; Wait after sending, so that queue is cleared for further commands.
      ;; (there would be no harm in letting the queue be extended
      ;; if it were allowed for).
      (progn
	(proof-shell-invisible-command
	 (format isar-usethy-notopml-command
		 (file-name-sans-extension buffer-file-name))
	 t)
	;; Leave the messages from the use around.
	(setq proof-shell-erase-response-flag nil))
    ))

(defun isar-shell-compute-new-files-list (str)
  "Compute the new list of files read by the proof assistant.
This is called when Proof General spots output matching
proof-shell-retract-files-regexp."
  ;; This assertion is supposed to test that we only remove
  ;; what was in the list anyway.  But 
  ;;(assert (member (file-truename (match-string 1 str))
  ;;		  proof-included-files-list))
  (remove (file-truename (match-string 1 str)) 
	  proof-included-files-list))

;;
;; Hack for update
;;

(defcustom isar-update-command "" ;; FIXME "ProofGeneral.update();"
  "Sent to Isabelle/Isar to re-load theory files as needed and synchronise."
  :type 'string
  :group 'isabelle-config)
  
(defun isar-update ()
  "Issue an update command to the Isabelle/Isar process.
This re-reads any theory files as necessary and resynchronizes
proof-included-files-list."
  (interactive)
  (save-some-buffers)
  (proof-shell-insert isar-update-command))

  



;;
;;   Define the derived modes 
;;
(eval-and-compile
(define-derived-mode isar-shell-mode proof-shell-mode
   "Isabelle/Isar shell" nil
   (isar-shell-mode-config)))

(eval-and-compile			; to define vars for byte comp.
(define-derived-mode isar-pbp-mode pbp-mode
  "Isabelle/Isar proofstate" nil
  (isar-pbp-mode-config)))

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
	 (proof-mark-buffer-atomic (current-buffer)))
    )
   (t 
    ;; Proof mode does that automatically.
    (isar-proofscript-mode))))

;; FIXME: could test that the buffer isn't already locked.
(defun isar-process-thy-file (file)
  "Process the theory file FILE.  If interactive, use buffer-file-name."
  (interactive (list buffer-file-name))
  (save-some-buffers)
  (proof-shell-invisible-command 
   (format isar-usethy-notopml-command
	   (file-name-sans-extension file))))

(defcustom isar-retract-thy-file-command "" ;; MMW FIXME "ML {| ProofGeneral.retract_thy_file \"%s\"; |};"
  "Sent to Isabelle/Isar to forget theory file and descendants.
Resulting output from Isabelle/Isar will be parsed by Proof General."
  :type 'string
  :group 'isabelle-isar-config)

(defcustom isar-retract-ML-file-command "" ;; MMW FIXME "ML {| ProofGeneral.retract_ML_file \"%s\"\"; |};"
  "Sent to Isabelle/Isar to forget ML file and descendants.
Resulting output from Isabelle/Isar will be parsed by Proof General."
  :type 'string
  :group 'isabelle-isar-config)

(defcustom isar-retract-ML-files-children-command "" ;; MMW FIXME "ProofGeneral.retract_ML_files_children \"%s\";"
  "Sent to Isabelle/Isar to forget the descendants of an ML file.
Resulting output from Isabelle will be parsed by Proof General."
  :type 'string
  :group 'isabelle-config)

(defun isar-retract-thy-file (file)
  "Retract the theory file FILE. If interactive, use buffer-file-name."
  (interactive (list buffer-file-name))
  (proof-shell-invisible-command
   (format isar-retract-thy-file-command
	   (file-name-sans-extension file))))


;; Next bits taken from isar-load.el
;; isar-load.el,v 3.8 1998/09/01 

(defgroup thy nil
  "Customization of Isamode's theory editing mode"
  ;; :link '(info-link "(Isamode)Theory Files")
  :load 'thy-mode
  :group 'isabelle-isar)

(autoload 'thy-mode "thy-mode" 
	  "Major mode for Isabelle/Isar theory files" t nil)

(autoload 'thy-find-other-file "thy-mode" 
	    "Find associated .ML or .thy file." t nil)

(defun isar-splice-separator (sep strings)
  (let (stringsep)
    (while strings
      (setq stringsep (concat stringsep (car strings)))
      (setq strings (cdr strings))
      (if strings (setq stringsep 
			(concat stringsep sep))))
    stringsep))

(defun isar-file-name-cons-extension (name)
  "Return cons cell of NAME without final extension and extension"
  (if (string-match "\\.[^\\.]+$" name)
      (cons (substring name 0 (match-beginning 0))
	    (substring name (match-beginning 0)))
    (cons name "")))

(defun isar-format (alist string)
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
(define-key isar-proofscript-mode-map 
  [(control c) (control o)] 'thy-find-other-file)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's Isabelle specific                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; FIXME: think about the next variable.  I've changed sense from
;;  LEGO and Coq's treatment.
(defcustom isar-not-undoable-commands-regexp
  (proof-ids-to-regexp '("break" "context" "clear_undo" "undo"))
  "Regular expression matching commands which are *not* undoable."
  :type 'regexp
  :group 'isabelle-isar-config)

;; This next function is the important one for undo operations.
(defun isar-count-undos (span)
  "Count number of undos in a span, return the command needed to undo that far."
  (let
      ((case-fold-search nil)
       (ct 0) str i)
    (if (and span (prev-span span 'type)
	     (not (eq (span-property (prev-span span 'type) 'type) 'comment))
	     (isar-goal-command-p
	      (span-property (prev-span span 'type) 'cmd)))
	(concat "top clear_undo" proof-terminal-string)
      (while span
	(setq str (span-property span 'cmd))
	(cond ((eq (span-property span 'type) 'vanilla)
	       (or (proof-string-match isar-not-undoable-commands-regexp str)
		   (setq ct (+ 1 ct))))
	      ((eq (span-property span 'type) 'pbp)
	       ;; this case probably redundant for Isabelle, unless
	       ;; we think of some nice ways of matching non-undoable
	       ;; commands.
	       (cond ((not (proof-string-match isar-not-undoable-commands-regexp str))
		      (setq i 0)
		      (while (< i (length str))
			(if (= (aref str i) proof-terminal-char)
			    (setq ct (+ 1 ct)))
			(setq i (+ 1 i))))
		     (t nil))))
	(setq span (next-span span 'type)))
      (concat "undos " (int-to-string ct) proof-terminal-string))))

(defun isar-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (proof-string-match isar-goal-command-regexp str)) ; this regexp defined in isar-syntax.el

;; Isabelle has no concept of a Linear context, so forgetting back
;; to the declaration of a particular something makes no real
;; sense.  Perhaps in the future there will be functions to remove
;; theorems from theories, but even then all we could do is
;; forget particular theorems one by one.  So we ought to search
;; backwards in isar-find-and-forget, rather than forwards as
;; the old code below does.

(defun isar-find-and-forget (span)
  "Return a command to be used to forget SPAN."
  (save-excursion
    ;; FIXME: bug here: too much gets retracted.
    ;; See if we are going to part way through a completely processed
    ;; buffer, in which case it should be removed from 
    ;; proof-included-files-list along with any other buffers
    ;; depending on it.  However, even though we send the retraction
    ;; command to Isabelle we don't want to *completely* unlock
    ;; the current buffer.  How can this be avoided?
    (goto-char (point-max))
    (skip-chars-backward " \t\n") 
    (if (>= (proof-unprocessed-begin) (point))
	(format isar-retract-ML-files-children-command 
		(file-name-sans-extension 
		 (file-name-nondirectory
		  (buffer-file-name))))
      proof-no-command)))


;; BEGIN Old code  (taken from Coq.el)
;(defconst isar-keywords-decl-defn-regexp
;  (ids-to-regexp (append isar-keywords-decl isar-keywords-defn))
;  "Declaration and definition regexp.")
;(defun isar-find-and-forget (span)
;  (let (str ans)
;    (while (and span (not ans))
;      (setq str (span-property span 'cmd))
;      (cond
;       ((eq (span-property span 'type) 'comment))       

;       ((eq (span-property span 'type) 'goalsave)
;	(setq ans (concat isar-forget-id-command
;			  (span-property span 'name) proof-terminal-string)))

;       ((string-match (concat "\\`\\(" isar-keywords-decl-defn-regexp
;                              "\\)\\s-*\\(" proof-id "\\)\\s-*[\\[,:]") str)
;	(setq ans (concat isar-forget-id-command
;			  (match-string 2 str) proof-terminal-string)))
;       ;; If it's not a goal but it contains "Definition" then it's a
;       ;; declaration
;       ((and (not (isar-goal-command-p str))
;	     (string-match
;	      (concat "Definition\\s-+\\(" proof-id "\\)\\s-*:") str))
;	(setq ans (concat isar-forget-id-command
;			  (match-string 2 str) proof-terminal-string))))
;      (setq span (next-span span 'type)))
;      (or ans "COMMENT")))
; END old code 

(defvar isar-current-goal 1
  "Last goal that emacs looked at.")

;; Parse proofstate output.  Isabelle does not display
;; named hypotheses in the proofstate output:  they
;; appear as a list in each subgoal.  Ignore
;; that aspect for now and just return the
;; subgoal number.
;; MMW FIXME: ??
(defun isar-goal-hyp ()
  (if (looking-at proof-shell-goal-regexp)
      (cons 'goal (match-string 1))))

(defun isar-state-preserving-p (cmd)
  "Non-nil if command preserves the proofstate."
  (proof-string-match isar-not-undoable-commands-regexp cmd))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Indentation                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; MMW FIXME: take from coq.el?
;; Sadly this is pretty pointless for Isabelle.
;; Proof scripts in Isabelle don't really have an easily-observed
;; block structure  -- a case split can be done by any obscure tactic,
;; and then solved in a number of steps that bears no relation to the
;; number of cases!  And the end is certainly not marked in anyway.
;; 
(defun isar-stack-to-indent (stack)
    (cond
   ((null stack) 0)
   ((null (car (car stack)))
    (nth 1 (car stack)))
   (t (save-excursion
	(goto-char (nth 1 (car stack)))
	(+ isabelle-isar-indent (current-column))))))

(defun isar-parse-indent (c stack)
  "Indentation function for Isabelle.  Does nothing at the moment."
  stack)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Isa shell startup and exit hooks                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isar-pre-shell-start ()
  (setq proof-prog-name		isabelle-isar-prog-name)
  (setq proof-mode-for-shell    'isar-shell-mode)
  (setq proof-mode-for-pbp	'isar-pbp-mode))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isar-init-syntax-table ()
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
  (setq blink-matching-paren-dont-ignore-comments t))


;; MMW FIXME: ??
;; This hook is added on load because proof shells can
;; be started from .thy (not in scripting mode) or .ML files.
(add-hook 'proof-pre-shell-start-hook 'isar-pre-shell-start nil t)

(defun isar-shell-mode-config ()
  "Configure Proof General proof shell for Isabelle/Isar."
  (isar-init-syntax-table)
  (isar-shell-mode-config-set-variables)
  (proof-shell-config-done)
  (isar-outline-setup))

;; FIXME: broken, of course, as is all PBP everywhere.
(defun isar-pbp-mode-config ()
  (setq pbp-change-goal "Show %s.")
  (setq pbp-error-regexp proof-shell-error-regexp)
  (isar-outline-setup))

(provide 'isar)
