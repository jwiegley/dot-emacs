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

(require 'proof)

(defconst isa-running-isar (eq proof-assistant-symbol 'isar))

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
      (let ((possibilities
	     '("isatool"
	       "/usr/bin/isatool"
	       "/usr/local/bin/isatool"
	       "/usr/lib/Isabelle/bin/isatool"
	       "/usr/lib/Isabelle99/bin/isatool"
	       "/usr/share/Isabelle/bin/isatool"
	       "/usr/share/Isabelle99/bin/isatool")))
	(while (and possibilities
		    (not (file-executable-p
			  (car possibilities))))
	  (setq possibilities (cdr possibilities)))
	(car-safe possibilities))
      "path_to_isatool_is_unknown")
  "Command to invoke Isabelle tool 'isatool'.
Use a full path name here if  isatool is not on PATH when Emacs is started."
  :type 'file
  :group 'isabelle)

(defun isa-set-isatool-command ()
  "Make sure isa-isatool-command points to a valid executable.
If it does not, prompt the user for the proper setting.
If it appears we're running on win32, allow this to remain unset.
Returns non-nil if isa-isatool-command is valid."
  (interactive)
  (while (unless proof-running-on-win32
	   (not (file-executable-p isa-isatool-command)))
    (beep)
    (setq isa-isatool-command
	  (read-file-name
	   "Please type in the full path to the `isatool' program: "
	   nil nil t)))
  (if (and proof-running-on-win32
	   (not (file-executable-p isa-isatool-command)))
      (warning "Proof General: isatool command not found; ignored because Win32 system detected."))
  (file-executable-p isa-isatool-command))

(defun isa-shell-command-to-string (command)
  "Like shell-command-to-string except the last character is stripped."
  (substring (shell-command-to-string command) 0 -1))

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

(defcustom isabelle-prog-name 
  (if (fboundp 'win32-long-file-name)	
      "C:\\sml\\bin\\.run\\run.x86-win32.exe @SMLload=C:\\Isabelle\\"
    "isabelle")
  "*Default name of program to run Isabelle.

The default value except when running under Windows is \"isabelle\".

The default value when running under Windows is:

  C:\\sml\\bin\\.run\\run.x86-win32.exe @SMLload=C:\\Isabelle\\

This expects SML/NJ in C:\\sml and Isabelle images in C:\Isabelle.  
The logic image name is tagged onto the end.  

NB: The Isabelle settings mechanism or the environment variable
ISABELLE will always override this setting."
  :type 'file
  :group 'isabelle)

(defun isa-tool-run-command (logic-name)
  "Make a command for running Isabelle using Isabelle tools.
This function is called with the name of the logic as an argument,
and builds a program name and arguments to run Isabelle."
  (let*
      ((default (if proof-running-on-win32
		    (concat isabelle-prog-name logic-name)
		  isabelle-prog-name))
       (commd	(isa-getenv "ISABELLE" default)))
    (cond
     (proof-running-on-win32		; Assume no special font there
      commd)
     (isa-use-special-font
      (concat commd "-misabelle_font" "-msymbols" logic-name))
     (t
      commd))))

(defun isa-tool-list-logics ()
  "Generate a list of available object logics."
  (if (isa-set-isatool-command)
      (split-string (isa-shell-command-to-string
		     (concat isa-isatool-command " findlogics")) "[ \t]")))

(defun isa-view-doc (docname)
  "View Isabelle document DOCNAME, using Isabelle tools."
  (if (isa-set-isatool-command)
      (apply 'start-process
	     "isa-view-doc" nil
	     (list isa-isatool-command "doc" docname))))

(defun isa-tool-list-docs ()
  "Generate a list of documentation files available, with descriptions.
This function returns a list of lists of the form
 ((DOCNAME DESCRIPTION) ....)
of Isabelle document names and descriptions.  When DOCNAME is
passed to isa-tool-doc-command, DOCNAME will be viewed."
  (if (isa-set-isatool-command)
      (mapcar
       (function (lambda (docdes)
		   (list
		    (substring docdes (string-match "\\(\\S-+\\)[ \t]+" docdes)
			       (match-end 1))
		    (substring docdes (match-end 0)))))
       (split-string
	(isa-shell-command-to-string
	 (concat isa-isatool-command " doc")) "\n"))))

(defun isa-tool-setup-font ()
  "Setup special font for isabelle, using Isabelle tools."
  (isa-set-isatool-command)
  (call-process isa-isatool-command nil nil nil "installfonts"))

(defun isa-default-logic-dir ()
  "Return a directory containing logic images."
   (car (split-string (isa-getenv "ISABELLE_PATH") ":")))

(defun isa-default-logic ()
  "Return the default logic."
  (or (isa-getenv "ISABELLE_LOGIC") "Pure"))

(defun isa-quit (save)
  "Quit / save the Isabelle session.
Called with one argument: t to save database, nil otherwise."
  (if (not save)
      (isa-insert-ret "quit();"))
  (comint-send-eof))

;;; Set proof-shell-pre-interrupt-hook for PolyML.
(if (and
     (not proof-shell-pre-interrupt-hook)
     (string-match "^polyml" (isa-getenv "ML_SYSTEM")))
    (add-hook
     'proof-shell-pre-interrupt-hook
     (lambda () (proof-shell-insert "f" nil))))

;;; ==========  Utility functions ==========

;; FIXME: a way of updating this list, please?
(defcustom isabelle-logics-available (isa-tool-list-logics)
  "*List of logics available to use with Isabelle.
If the `isatool' program is available, this is automatically
generated."
  :type (list 'string)
  :group 'isabelle)
  
;; FIXME: type here needs to be dynamic based on isabelle-logics-avalable
;; Is that possible?
;; Otherwise it should be updated on re-loading.
(defcustom isabelle-logic "HOL"
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
    (list (cons "Isatool Docs" (mapcar vc (isa-tool-list-docs)))))
  "Isabelle documentation menu.  Constructed dynamically.")



;;; ========== Mirroring Proof General options in Isabelle process ========

;; NB: EXPERIMENTAL: this pattern to be generalised to all provers via
;; some extra macros

;; Use of defasscustom and proof-ass-sym here gives separate customizable
;; options for Isabelle and Isabelle/Isar.

(proof-defasscustom show-types  nil
  "Whether to show types in Isabelle."
  :type 'boolean
  :set 'proof-set-value)

(proof-defassfun show-types ()
  (isa-proof-invisible-command-ifposs 
   (isabelle-set-default-cmd 'show-types)))

(proof-defasscustom show-sorts  nil
  "Whether to show sorts in Isabelle."
  :type 'boolean
  :set 'proof-set-value)

(proof-defassfun show-sorts ()
  (isa-proof-invisible-command-ifposs 
   (isabelle-set-default-cmd 'show-sorts)))

(proof-defasscustom show-consts  nil
  "Whether to show types of consts in Isabelle goals."
  :type 'boolean
  :set 'proof-set-value)

(proof-defassfun show-consts ()
  (isa-proof-invisible-command-ifposs 
   (isabelle-set-default-cmd 'show-consts)))

(proof-defasscustom long-names  nil
  "Whether to show fully qualified names in Isabelle."
  :type 'boolean
  :set 'proof-set-value)

(proof-defassfun long-names ()
  (isa-proof-invisible-command-ifposs 
   (isabelle-set-default-cmd 'long-names)))

(proof-defasscustom trace-simplifier  nil
  "Whether to trace the Simplifier in Isabelle."
  :type 'boolean
  :set 'proof-set-value)

(proof-defassfun trace-simplifier ()
  (isa-proof-invisible-command-ifposs 
   (isabelle-set-default-cmd 'trace-simplifier)))

(defun isa-proof-invisible-command-ifposs (cmd)
  ;; Better would be to queue the command, or even interrupt a queue
  ;; in progress.  Also must send current settings at start
  ;; of session somehow.  (This might happen automatically if
  ;; a queue of deffered commands is set, since defcustom calls
  ;; proof-set-value even to set the default/initial value?)
  (if (proof-shell-available-p)
      (progn
	(proof-shell-invisible-command cmd t)
	;; refresh display, FIXME: should only do if goals display is active,
	;; messy otherwise. 
	;; (we need a new flag for "active goals display").  
	;; (proof-prf) 
	;;  Could also repeat last command if non-state destroying.
	)))

(defun isar-markup-ml (string)
  "Return marked up version of STRING for Isar if we seem to be using Isar."
  (if isa-running-isar (format "ML_command {* %s *}; pr;" string) string))

(defun isa-format-bool (string val)
  (isar-markup-ml
   (proof-format (list (cons "%b" (if val "true" "false"))) string)))

(defcustom isabelle-default-values-list 
  '((show-types  
     . (isa-format-bool "show_types:=%b;" (proof-ass show-types)))
    (show-sorts 
     . (isa-format-bool "show_sorts:=%b;" (proof-ass show-sorts)))
    (show-consts
     . (isa-format-bool "show_consts:=%b;" (proof-ass show-consts)))
    (long-names
     . (isa-format-bool "long_names:=%b;" (proof-ass long-names)))
    (trace-simplifier
     . (isa-format-bool "trace_simp:=%b;" (proof-ass trace-simplifier))))
  "A list of default values kept in Proof General which are sent to Isabelle."
  :type 'sexp
  :group 'isabelle-config)


(defun isabelle-set-default-cmd (&optional setting)
  "Return a string for setting default values kept in Proof General customizations.
If SETTING is non-nil, return a string for just that setting. 
Otherwise return a string for configuring all settings."
  (let
      ((evalifneeded (lambda (expr)
			(if (or (not setting) (eq setting (car expr)))
			    (eval (cdr expr))))))
    (apply 'concat (mapcar evalifneeded 
			   isabelle-default-values-list))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Generic Isabelle menu for Isabelle and Isabelle/Isar
;;

(proof-deftoggle-fn (proof-ass-sym show-types))
(proof-deftoggle-fn (proof-ass-sym show-sorts))
(proof-deftoggle-fn (proof-ass-sym show-consts))
(proof-deftoggle-fn (proof-ass-sym long-names))
(proof-deftoggle-fn (proof-ass-sym trace-simplifier))

(proof-defass-default menu-entries
  (append
   (if isa-running-isar
       nil
     (list
      ["Switch to theory" thy-find-other-file t]
      "----"))
   `(["Show types" ,(proof-ass-sym show-types-toggle)
     :style toggle
     :selected ,(proof-ass-sym show-types)]
     ["Show sorts"  ,(proof-ass-sym show-sorts-toggle)
      :style toggle
      :selected ,(proof-ass-sym show-sorts)]
     ["Show consts"  ,(proof-ass-sym show-consts-toggle)
      :style toggle
      :selected ,(proof-ass-sym show-consts)]
     ["Long names"  ,(proof-ass-sym long-names-toggle)
      :style toggle
      :selected ,(proof-ass-sym long-names)]
     ["Trace simplifier" ,(proof-ass-sym trace-simplifier-toggle)
      :style toggle
      :selected ,(proof-ass-sym trace-simplifier)])))

(proof-defass-default help-menu-entries isabelle-docs-menu)


(provide 'isabelle-system)
;; End of isabelle-system.el
