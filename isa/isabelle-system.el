;; isabelle-system.el Interface with Isabelle system
;;
;; Copyright (C) 2000 LFCS Edinburgh, David Aspinall. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; Most of this code is taken from the final version of Isamode.
;; --------------------------------------------------------------
;;

(require 'proof)			; for proof-assistant-symbol, etc.
(require 'proof-syntax)			; for proof-string-match

(defconst isa-running-isar 
  (eq proof-assistant-symbol 'isar))

;; If we're using Isabelle/Isar then the isabelle custom
;; group won't have been defined yet.
(if isa-running-isar
(defgroup isabelle nil
  "Customization of user options for Isabelle and Isabelle/Isar Proof General"
  :group 'proof-general))

(defcustom isabelle-web-page
  "http://www.cl.cam.ac.uk/Research/HVG/Isabelle/"
  ;; "http://isabelle.in.tum.de"
  ;; "http://www.dcs.ed.ac.uk/home/isabelle"
  "URL of web page for Isabelle."
  :type 'string
  :group 'isabelle)


;;; ================ Extract Isabelle settings ================

(defcustom isa-isatool-command
  (or (getenv "ISATOOL") 
      (proof-locate-executable "isatool")
      ;; FIXME: use same mechanism as isabelle-program-name below.
      (let ((possibilities
	     (list
	      (concat (getenv "HOME") "/Isabelle/bin/isatool")
	      "/usr/share/Isabelle/bin/isatool"
	      "/usr/local/bin/isatool"
	      "/usr/local/Isabelle/bin/isatool"
	      "/usr/bin/isatool"
	      "/opt/bin/isatool"
	      "/opt/Isabelle/bin/isatool")))
	(while (and possibilities
		    (not (file-executable-p
			  (car possibilities))))
	  (setq possibilities (cdr possibilities)))
	(car-safe possibilities))
      "path_to_isatool_is_unknown")
  "Command to invoke Isabelle tool 'isatool'.
XEmacs should be able to find `isatool' if it is on the PATH when
started.  Then several standard locations are attempted.
Otherwise you should set this, using a full path name here for reliable 
working."
  :type 'file
  :group 'isabelle)

(defvar isatool-not-found nil
  "Non-nil if user has been prompted for `isatool' already and it wasn't found.")

(defun isa-set-isatool-command ()
  "Make sure isa-isatool-command points to a valid executable.
If it does not, prompt the user for the proper setting.
If it appears we're running on win32 or FSF Emacs, we allow this to
remain unverified.
Returns non-nil if isa-isatool-command is surely an executable
with full path."
  (interactive)
  (unless (or isatool-not-found (file-executable-p isa-isatool-command))
    (setq isa-isatool-command
	  (read-file-name
	   "Please give the full path to `isatool' (RET if you don't have it): "
	   nil nil nil))
    (if (not (file-executable-p isa-isatool-command))
	(progn
	  (setq isatool-not-found t)
	  (beep)
	  (warn "Proof General: isatool command not found; some menus will be incomplete."))))
  (file-executable-p isa-isatool-command))

(defun isa-shell-command-to-string (command)
  "Like shell-command-to-string except the last character is stripped."
  (let ((s (shell-command-to-string command)))
    (if (equal (length s) 0) s
      (substring s -1))))

(defun isa-getenv (envvar &optional default)
  "Extract an environment variable setting using the `isatool' program.
If the isatool command is not available, try using elisp's getenv
to extract the value from Emacs' environment.
If there is no setting for the variable, DEFAULT will be returned"
  (isa-set-isatool-command)
  (if (file-executable-p isa-isatool-command)
      (let ((setting (isa-shell-command-to-string
		      (concat isa-isatool-command
			      " getenv -b " envvar))))
	(if (string-equal setting "")
	    default
	  setting))
    (or (getenv envvar) default)))

;;;
;;; ======= Interaction with System using Isabelle tools =======
;;;

(defcustom isabelle-program-name 
  (if (fboundp 'proof-running-on-win32)	
      "C:\\sml\\bin\\.run\\run.x86-win32.exe @SMLload=C:\\Isabelle\\"
    (proof-locate-executable "isabelle" t
			     '("/usr/local/Isabelle/bin/"
			       "/opt/Isabelle/bin/"
			       "/usr/Isabelle/bin/"
			       "/usr/share/Isabelle/bin/")))
  "*Default name of program to run Isabelle.

The default value except when running under Windows is \"isabelle\",
which will get expanded using PATH if possible, or in a number
of standard locations (/usr/local/Isabelle/, /opt/Isabelle, etc). 

The default value when running under Windows is:

  C:\\sml\\bin\\.run\\run.x86-win32.exe @SMLload=C:\\Isabelle\\

This expects SML/NJ in C:\\sml and Isabelle images in C:\Isabelle.  
The logic image name is tagged onto the end.  

NB: The Isabelle settings mechanism or the environment variable
ISABELLE will always override this setting."
  :type 'file
  :group 'isabelle)

(defvar isabelle-prog-name isabelle-program-name
  "Set from `isabelle-program-name', has name of logic appended sometimes.")

(defun isabelle-command-line ()
  "Make proper command line for running Isabelle"
  (let*
      ;; The ISABELLE and PROOFGENERAL_LOGIC values (as set when run
      ;; under the interface wrapper script) indicate that we should
      ;; determine the proper command line from the current Isabelle
      ;; settings environment.
      ((isabelle (or
		  (getenv "ISABELLE")	; overrides default, may be updated
		  isabelle-program-name ; calculated earlier
		  "isabelle"))		; to be really sure
       (isabelle-opts (getenv "ISABELLE_OPTIONS"))
       (opts (concat
	      (if isa-running-isar " -PI" "")
	      (if (and isabelle-opts (not (equal isabelle-opts "")))
		  (concat " " isabelle-opts) "")))
       (logic (or isabelle-chosen-logic
		  (getenv "PROOFGENERAL_LOGIC")))
       (logicarg (if (and logic (not (equal logic "")))
		     (concat " " logic) "")))
    (concat isabelle opts logicarg)))


(defun isabelle-choose-logic (logic)
  "Adjust isabelle-prog-name and proof-prog-name for running LOGIC."
  (interactive 
   (list (completing-read 
	  "Use logic: "
	  (mapcar 'list (cons "Default" 
			      isabelle-logics-available)))))
  ;; a little bit obnoxious maybe (but maybe what naive user would expect)
  ;; (customize-save-variable 'isabelle-chosen-logic logic)
  (if (proof-shell-live-buffer)
      (error "Can't change logic while Isabelle is running, please exit process first!"))
  (customize-set-variable 'isabelle-chosen-logic 
			  (unless (string-equal logic "Default") logic))
  (setq isabelle-prog-name (isabelle-command-line))
  (setq proof-prog-name isabelle-prog-name)
  ;; Settings are potentially different between logics, and
  ;; so are Isar keywords.  Set these to nil so they get
  ;; automatically re-initialised.  
  ;; FIXME: Isar keywords change not handled yet.
  (setq proof-assistant-settings nil)
  (setq proof-menu-settings nil))

(defun isa-tool-list-logics ()
  "Generate a list of available object logics."
  (if (isa-set-isatool-command)
      (delete "" (split-string 
		  (isa-shell-command-to-string
		   (concat isa-isatool-command " findlogics")) "[ \t]"))))

(defun isa-view-doc (docname)
  "View Isabelle document DOCNAME, using Isabelle tools."
  (if (isa-set-isatool-command)
      (apply 'start-process
	     "isa-view-doc" nil
	     (list isa-isatool-command "doc" docname))))

(defvar isabelle-version-string 'unset)

(defun isa-version ()
  "Try to retrieve a version value for Isabelle."
  (unless (stringp isabelle-version-string)
    (setq isabelle-version-string
	  (if (isa-set-isatool-command)
	      (isa-shell-command-to-string
	       ;; This may return the string "Unknown Isabelle tool:
	       ;; version", but that's fine.
	       (concat isa-isatool-command " version"))
	    "Unknown")))
  isabelle-version-string)

;; We're going to need to know this pretty soon, so let's do it now.
(defconst isa-supports-pgip 
  ;; PGIP-aware Isabelle versions are also aware of their own version
  (not (string-match "^Unknown" (isa-version)))
  "Whether the currently configured version of Isabelle supports PGIP.")

      


(defun isa-tool-list-docs ()
  "Generate a list of documentation files available, with descriptions.
This function returns a list of lists of the form
 ((DOCNAME DESCRIPTION) ....)
of Isabelle document names and descriptions.  When DOCNAME is
passed to isa-tool-doc-command, DOCNAME will be viewed."
  (if (isa-set-isatool-command)
      (let ((docs (isa-shell-command-to-string
		   (concat isa-isatool-command " doc"))))
	(unless (string-equal docs "")
	  (mapcan
	   (function (lambda (docdes)
		       (if (proof-string-match "^[ \t]+\\(\\S-+\\)[ \t]+" docdes)
			   (list (list 
				  (substring docdes (match-beginning 0) (match-end 1))
				  (substring docdes (match-end 0)))))))
	   (split-string docs "\n"))))))

(defun isa-quit (save)
  "Quit / save the Isabelle session.
Called with one argument: t to save database, nil otherwise."
  (if (not save)
      (isa-insert-ret "quit();"))
  (comint-send-eof))

(defconst isabelle-verbatim-regexp "\\`\^VERBATIM: \\(\\(.\\|\n\\)*\\)\\'"
  "Regexp matching internal marker for verbatim command output")

(defun isabelle-verbatim (str)
  "Mark internal command for verbatim output"
  (concat "\^VERBATIM: " str))

;;; Set proof-shell-pre-interrupt-hook for PolyML 3.
(if (and
     (not proof-shell-pre-interrupt-hook)
     ;; (Older versions of Isabelle reported PolyML for PolyML 3).
     (proof-string-match-safe "\\`polyml" (isa-getenv "ML_SYSTEM"))
     (not (proof-string-match-safe "\\`polyml-4" (isa-getenv "ML_SYSTEM"))))
    (add-hook
     'proof-shell-pre-interrupt-hook
     (lambda () (proof-shell-insert (isabelle-verbatim "f") nil))))

;;; ==========  Utility functions ==========

(defcustom isabelle-refresh-logics t
  "*Whether to refresh the list of logics during an interactive session.
If non-nil, then `isatool findlogics' will be used to regenerate
the `isabelle-logics-available' setting.  If this tool does not work
for you, you should disable this behaviour."
  :type 'boolean
  :group 'isabelle)

(defcustom isabelle-logics-available (isa-tool-list-logics)
  "*List of logics available to use with Isabelle.
If the `isatool' program is available, this is automatically
generated with the lisp form `(isa-tool-list-logics)'."
  :type (list 'string)
  :group 'isabelle)

;; FIXME: document this one
(defcustom isabelle-chosen-logic nil
  "*Choice of logic to use with Isabelle.
If non-nil, will be added into isabelle-prog-name as default value.

NB: you have saved a new logic image, it may not appear in the choices
until Proof General is restarted."
  :type (append
	 (list 'choice)
	 (mapcar (lambda (str) (list 'const str)) isabelle-logics-available)
	 (list '(string :tag "Choose another")
	       '(const :tag "Unset (use default)" nil)))
  :group 'isabelle)

(defconst isabelle-docs-menu 
  (let ((vc '(lambda (docdes)
	       (vector (car (cdr docdes))
		       (list 'isa-view-doc (car docdes)) t))))
    (list (cons "Isabelle documentation" (mapcar vc (isa-tool-list-docs)))))
  "Isabelle documentation menu.  Constructed when PG is loaded.")


;; PG 3.5: logics menu is now refreshed automatically.  Rather
;; a big effort for such a small effect.
(defun isabelle-logics-menu-calculate ()
  (setq isabelle-logics-menu-entries
	(cons "Logics"
	      (append
	       '(["Default" 
		  (isabelle-choose-logic nil)
		  :active (not (proof-shell-live-buffer))
		  :style radio
		  :selected (not isabelle-chosen-logic)])
	       (mapcar (lambda (l) 
		   (vector l (list 'isabelle-choose-logic l)
			   :active '(not (proof-shell-live-buffer))
			   :style 'radio
			   :selected (list 'equal 'isabelle-chosen-logic l)))
		       isabelle-logics-available)))))

(defvar isabelle-time-to-refresh-logics t
  "Non-nil if we should refresh the logics list")

(defun isabelle-logics-menu-refresh ()
  "Refresh isabelle-logics-menu-entries, returning new entries."
  (interactive)
  (if (and isabelle-refresh-logics
	   (or isabelle-time-to-refresh-logics (interactive-p)))
      (progn
	(setq isabelle-logics-available (isa-tool-list-logics))
	(isabelle-logics-menu-calculate)
	(if proof-running-on-Emacs21 
	    ;; update the menu manually
	    (easy-menu-add-item proof-assistant-menu nil 
				isabelle-logics-menu-entries))
	(setq isabelle-time-to-refresh-logics nil) ;; just done it, don't repeat!
	(run-with-timer 2 nil ;; short delay to avoid doing this too often
			(lambda () (setq isabelle-time-to-refresh-logics t))))))

;; Function for XEmacs only
(defun isabelle-logics-menu-filter (&optional ignored)
  (isabelle-logics-menu-refresh)
  (cdr isabelle-logics-menu-entries))

;; Functions for GNU Emacs only to update logics menu
(if proof-running-on-Emacs21
(defun isabelle-menu-bar-update-logics ()
  ;; standard check we're being invoked
  (and (current-local-map)
       (keymapp (lookup-key (current-local-map) 
 			    (vector 'menu-bar (intern proof-assistant))))
       (isabelle-logics-menu-refresh))))

(if proof-running-on-Emacs21
    (add-hook 'menu-bar-update-hook 'isabelle-menu-bar-update-logics))


(defvar isabelle-logics-menu-entries (isabelle-logics-menu-calculate))

(defvar isabelle-logics-menu 
   (if proof-running-on-XEmacs
       (cons (car isabelle-logics-menu-entries)
	     (list :filter 'isabelle-logics-menu-filter)) ;; generates menu on click
     isabelle-logics-menu-entries)
  "Isabelle logics menu.  Calculated when Proof General is loaded.")

;; Added in PG 3.4: load isar-keywords file.
;; This roughly follows the method given in the interface script.
;; It could be used to add an elisp command at the bottom of
;; a theory file, if we sorted out the load order a bit, or
;; added a facility to reconfigure.
;; TODO: also add something to spill out a keywords file?
(defun isabelle-load-isar-keywords (&optional kw)
  (interactive "sLoad isar keywords: ")
  (let ((userhome  (isa-getenv "ISABELLE_HOME_USER"))
	(isahome   (isa-getenv "ISABELLE_HOME"))
	(isarkwel  "%s/etc/isar-keywords-%s.el")
	(isarel    "%s/etc/isar-keywords.el")
	(ifrdble   (lambda (f) (if (file-readable-p f) f))))
    (load-file
     (or
      (and kw (funcall ifrdble (format isarkwel userhome kw)))
      (and kw (funcall ifrdble (format isarkwel isahome kw)))
      (funcall ifrdble (format isarel userhome))
      (funcall ifrdble (format isarel isahome))
      (locate-library "isar-keywords")))))


;;; ========== Mirroring Proof General options in Isabelle process ========

;; NB: use of defpacustom here gives  separate customizable
;; options for Isabelle and Isabelle/Isar.

;; In latest release of Isabelle, these are set automatically via PGIP
;; sent from Isabelle.

;; BEGIN backwards compatibility 
(cond 
 ((not isa-supports-pgip)
(defpacustom show-types  nil
  "Whether to show types in Isabelle."
  :type 'boolean
  :setting "show_types:=%b;")

(defpacustom show-sorts  nil
  "Whether to show sorts in Isabelle."
  :type 'boolean
  :setting "show_sorts:=%b;")

(defpacustom show-consts  nil
  "Whether to show types of consts in Isabelle goals."
  :type 'boolean
  :setting "show_consts:=%b;")

(defpacustom long-names  nil
  "Whether to show fully qualified names in Isabelle."
  :type 'boolean
  :setting "long_names:=%b;")

(defpacustom eta-contract  t
  "Whether to print terms eta-contracted in Isabelle."
  :type 'boolean
  :setting "Syntax.eta_contract:=%b;")

(defpacustom trace-simplifier  nil
  "Whether to trace the Simplifier in Isabelle."
  :type 'boolean
  :setting "trace_simp:=%b;")

(defpacustom trace-rules  nil
  "Whether to trace the standard rules in Isabelle."
  :type 'boolean
  :setting "trace_rules:=%b;")

(defpacustom quick-and-dirty  t
  "Whether to take a few short cuts occasionally."
  :type 'boolean
  :setting "quick_and_dirty:=%b;")

(defpacustom full-proofs  nil
  "Whether to record full proof objects internally."
  :type 'boolean
  :setting "Library.error_fn := (fn _ => ()); Library.try (fn () => Context.use_mltext \"ProofGeneral.full_proofs %b;\" false Library.None) ();")
;FIXME should become "ProofGeneral.full_proofs %b;" next time

(defpacustom global-timing  nil
  "Whether to enable timing in Isabelle."
  :type 'boolean
  :setting "Library.timing:=%b;")

(if proof-experimental-features
(defpacustom theorem-dependencies nil
  "Whether to track theorem dependencies within Proof General."
  :type 'boolean
  :setting ("print_mode := ([\"thm_deps\"] @ ! print_mode);" .
	    "print_mode := (Library.gen_rems (op =) (! print_mode, [\"thm_deps\"]));")))

(defpacustom goals-limit  10
  "Setting for maximum number of goals printed in Isabelle."
  :type 'integer
  :setting "goals_limit:=%i;")

(defpacustom prems-limit  10
  "Setting for maximum number of premises printed in Isabelle/Isar."
  :type 'integer
  :setting "ProofContext.prems_limit:=%i;")

(defpacustom print-depth  10
  "Setting for the ML print depth in Isabelle."
  :type 'integer
  :setting "print_depth %i;")))
;; END backwards compatibility 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Generic Isabelle menu for Isabelle and Isabelle/Isar
;;

(defpgdefault menu-entries
  (append
   (if isa-running-isar
       nil
     (list ["Switch to theory" thy-find-other-file t]))
   (list isabelle-logics-menu)))

(defpgdefault help-menu-entries isabelle-docs-menu)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; X-Symbol language configuration, and adding to completion table
;;

(defpgdefault x-symbol-language 'isabelle)


(eval-after-load "x-symbol-isabelle"
 ;; Add x-symbol tokens to isa-completion-table and rebuild
 ;; internal completion table if completion is already active
'(progn
   (defpgdefault completion-table
     (append (proof-ass completion-table)
	     (mapcar (lambda (xsym) (nth 2 xsym))
		     x-symbol-isabelle-table)))
   (setq proof-xsym-font-lock-keywords
	 x-symbol-isabelle-font-lock-keywords)
   (if (featurep 'completion)
       (proof-add-completions))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Subterm markup -- faking it
;;

(defun isabelle-convert-idmarkup-to-subterm ()
  "Convert identifier markup to subterm markup.
This is a hook setting for `pg-after-fontify-output-hook' to
enable identifiers to be highlighted.  (To disable that behaviour,
the function `pg-remove-specials' can be used instead)."
  ;; NB: the order of doing this is crucial: it must happen after
  ;; fontifying (since replaces chars used for fontifying), but before
  ;; X-Sym decoding (since some chars used for fontifying may clash
  ;; with X-Sym character codes: luckily those codes don't seem to
  ;; cause problems for subterm markup).
  ;; Future version of this should use PGML output in Isabelle2002.
  (goto-char (point-min))
  (while (re-search-forward 
	  "\351\\|\352\\|\353\\|\354\\|\355\\|\356\\|\357" nil t)
    (replace-match "\372\200\373" nil t))
  (goto-char (point-min))
  (while (re-search-forward "\350" nil t)
    (replace-match "\374" nil t)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Context-senstive in-span menu additions 
;;

(defun isabelle-create-span-menu (span idiom name)
  (if (string-equal idiom "proof")
      (let ((thm (span-property span 'name)))
	(list (vector 
	       "Visualise dependencies" 
	       `(proof-shell-invisible-command 
		 ,(format (if isa-running-isar 
			      "thm_deps %s;" "thm_deps [%s];") thm))
	       (not (string-equal thm proof-unnamed-theorem-name)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; XML as an SML string: add escapes for quotes
;;

(defun isabelle-xml-sml-escapes (xmlstring)
  (replace-regexp-in-string "\"" "\\\"" xmlstring t t))

(defun isabelle-process-pgip (xmlstring)
  "Return an Isabelle or Isabelle/Isar command to process PGIP in XMLSTRING."
  (if isa-supports-pgip
      (let ((mlcmd (format "ProofGeneral.process_pgip(\"%s\");"
			   (isabelle-xml-sml-escapes xmlstring))))
	(if (eq proof-assistant-symbol 'isar)
	    (isar-markup-ml mlcmd)
	  mlcmd))
    "")) ;; Empty string in case called with non PGIP-aware Isabelle.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Understanding syntax configuration (really should be PGIP, but...)
;;
;; [PRESENTLY UNUSED; WORK IN PROGRESS]

(defun isabelle-parse-syntax-dump (buf)
  (save-excursion
    (let (consts start lim)
      (set-buffer buf)
      (goto-char (point-min))
      (if (re-search-forward "consts:" nil t)
	  (progn
	    (setq start (point))
	    (setq lim (re-search-forward "parse_ast_translation:" nil t))
	    (goto-char start)
	    (while (re-search-forward "\"\\([^\"]*\\)\"" lim t)
	      (if (< 0 (length (match-string 1)))
		  (setq consts (cons (match-string 1) consts))))))
      consts)))


(provide 'isabelle-system)
;; End of isabelle-system.el
