;; proof-site.el --- Configuration for site and choice of prover.
;;
;; Copyright (C) 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Thomas Kleymann
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>
;;
;; $Id$
;;

(or (featurep 'custom)
    ;; Quick hack to support defcustom for Emacs 19
    (defmacro defcustom (sym val doc &rest args)
      (defvar sym val doc))
    (defmacro group (sym mems doc &rest args)))

(defgroup proof-general nil
  "Customization of generic parameters for Proof General."
  :group 'external
  :group 'processes)

(defcustom proof-home
  ;; FIXME: make sure compiling does not evaluate next expression.
  (or (getenv "PROOF_HOME") 
      (let ((curdir 
	     (or
	      (and load-in-progress (file-name-directory load-file-name))
	      (file-name-directory (buffer-file-name)))))
	(file-name-directory (substring curdir 0 -1))))
  "*Directory where Proof General is installed. Ends with slash.
Default value taken from environment variable PROOF_HOME if set, 
otherwise based on where the file proof-site was loaded from.
You can use customize to set this variable."
  :type 'directory
  :group 'proof-general)

(defcustom proof-image-directory
  (concat proof-home "images/")
    "*Where Proof General image files are installed. Ends with slash."
  :type 'directory
  :group 'proof-general)

(defcustom proof-info-dir 
  (concat proof-home "doc/")
  "*Where Proof General Info files are installed."
  :type 'directory
  :group 'proof-general)

;; Add the info directory to the end of Emacs Info path 
;; if need be. 
(or (memq proof-info-dir Info-default-directory-list)
    (setq Info-default-directory-list
	  (append 
	   Info-default-directory-list 
	   (list proof-info-dir))))

(defconst proof-general-supported-assistants
  '((isa	"Isabelle"	"\\.ML$\\|\\.thy$")
    (lego	"LEGO"		"\\.l$")
    (coq	"Coq"		"\\.v")
    (myass	"myass"		"\\.myass"))
  "Table of supported proof assistants.
Each entry is a list of the form

    (SYMBOL NAME AUTOLOAD-REGEXP)

The NAME is a string, naming the proof assistant.
The SYMBOL is used to form the name of the mode for the
assistant, `SYMBOL-mode`, run when files with AUTOLOAD-REGEXP
are loaded.  It is also used to form the name of the
directory and elisp file for the mode, which will be
 
    <proof-home>/SYMBOL/SYMBOL.el

where `<proof-home>/' is the value of the variable proof-home.")

(defcustom proof-assistants
  (mapcar (lambda (astnt) (car astnt)) proof-general-supported-assistants)
  (concat
   "*Choice of proof assitants to use with Proof General.
A list of symbols chosen from " 
   (apply 'concat (mapcar (lambda (astnt) 
			    (concat "'" (symbol-name (car astnt)) " "))
			  proof-general-supported-assistants)) 
"\nNB: To change proof assistant, you must start a new Emacs session.")
  :type (cons 'set 
	      (mapcar (lambda (astnt)
			(list 'const ':tag (car (cdr astnt)) (car astnt)))
		      proof-general-supported-assistants))
  :group 'proof-general)

;; Extend load path for the generic files.
(setq load-path
      (cons (concat proof-home "generic/") load-path))


;; Now add auto-loads and load-path elements to support the 
;; proof assistants selected
(let ((assistants proof-assistants) proof-assistant)
  (while assistants
    (let*  
	((proof-assistant (car assistants))
	 (nameregexp 
	  (or 
	   (cdr-safe 
	    (assoc proof-assistant proof-general-supported-assistants))
	   (error "proof-site: symbol " (symbol-name proof-assistant) 
		  "is not in proof-general-supported-assistants")))
	 (assistant-name (car nameregexp))
	 (regexp	 (car (cdr nameregexp)))
	 (sname		 (symbol-name proof-assistant))
	 ;; NB: File name for each prover is the same as its symbol name!
	 (elisp-file   sname)
	 ;; NB: Dir name for each prover is the same as its symbol name!
	 (elisp-dir    sname)
	 ;; NB: Mode name for each prover is <symname>-mode!
	 (proofgen-mode  (intern (concat sname "-mode"))))

      (setq auto-mode-alist 
	    (cons (cons regexp proofgen-mode) auto-mode-alist))
      (autoload proofgen-mode elisp-file
	(concat
	 "Major mode for editing scripts for proof assistant " 
	 assistant-name ".")
	t)
      (setq load-path 
	    (cons (concat proof-home elisp-dir "/") load-path))
      (setq assistants (cdr assistants))
      ;; Developer's note: would be nice to add the customization group
      ;; <sname>-settings for a particular assistant here, 
      ;; but currently that could cause problems with more than one 
      ;; instance of Proof General being loaded.  For the time being
      ;; you have to visit a file before the specific prover's
      ;; customizations appear.
      )))

;; WARNING: do not edit below here 
;; (the next constant is set automatically)
(defconst proof-general-version
 "Proof General, Version 2.0-pre980910 released by da,tms. Email lego@dcs.ed.ac.uk."
 "Version string for Proof General.")

(provide 'proof-site)


		 
  


      

