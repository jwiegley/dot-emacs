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
;; FIXME 2: why is this quoted in the customize buffer??
;; (maybe the right thing, but seems odd)
(defcustom isabelle-logics-available (isa-tool-list-logics)
  "*List of logics available to use with Isabelle.
If the `isatool' program is available, this is automatically
generated with the lisp form `(isa-tool-list-logics)'."
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

;; NB: use of defpacustom here gives  separate customizable
;; options for Isabelle and Isabelle/Isar.

(defpacustom show-types  nil
  "Whether to show types in Isabelle."
  :type 'boolean
  :setting "show_types:=%b;")

(defpacustom show-sorts  nil
  "Whether to show sorts in Isabelle."
  :type 'boolean
  :setting "show_types:=%b;")

(defpacustom show-consts  nil
  "Whether to show types of consts in Isabelle goals."
  :type 'boolean
  :setting "show_consts:=%b;")

(defpacustom long-names  nil
  "Whether to show fully qualified names in Isabelle."
  :type 'boolean
  :setting "long_names:=%b;")

(defpacustom trace-simplifier  nil
  "Whether to trace the Simplifier in Isabelle."
  :type 'boolean
  :setting "trace_simp:=%b;")

(defpacustom print-depth  10
  "Setting for the ML print depth in Isabelle."
  :type 'integer
  :setting "print_depth %i;")

;; FIXME: move this somewhere sensible.
;; (actually only needs setting for isar)
(setq proof-assistant-setting-format 'isar-markup-ml)

(defun isar-markup-ml (string)
  "Return marked up version of STRING for Isar if we seem to be using Isar."
  (if isa-running-isar (format "ML_command {* %s *};" string) string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Generic Isabelle menu for Isabelle and Isabelle/Isar
;;

(defpgdefault menu-entries
  (if isa-running-isar
      nil
    (list ["Switch to theory" thy-find-other-file t])))

(defpgdefault help-menu-entries isabelle-docs-menu)


(provide 'isabelle-system)
;; End of isabelle-system.el
