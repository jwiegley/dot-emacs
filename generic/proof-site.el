;; proof-site.el -- Configuration for site and choice of provers.
;;
;; Copyright (C) 1998 LFCS Edinburgh. 
;; Author: David Aspinall
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;

;; begin UGLY COMPATIBILITY HACK
(or (featurep 'custom)
    ;; Quick hack to support defcustom for Emacs 19
    ;; FIXME da: Remove this soon.
    ;; Customize works fine with Emacs 20.2
    (defmacro defcustom (sym val doc &rest args)
      (defvar sym val doc))
    (defmacro group (sym mems doc &rest args)))
;; end UGLY COMPATIBILITY HACK


(defgroup proof nil
  "Customization of Proof General."
  :group 'external
  :group 'processes)


;; This customization group gathers together
;; the internals of Proof General which control
;; configuration to different proof assistants.
;; This is for development purposes rather than
;; user-level customization, so this group does
;; not belong to 'proof (or any other group).
(defgroup proof-internal nil
  "Customization of Proof General internals.")


;; Master table of supported assistants.
(defcustom proof-internal-assistant-table
  '((isa	"Isabelle"	"\\.ML$\\|\\.thy$")
    (lego	"LEGO"		"\\.l$")
    (coq	"Coq"		"\\.v$"))
  "Proof General's table of supported proof assistants.
Extend this table to add a new proof assistant.
Each entry is a list of the form

    (SYMBOL NAME AUTOMODE-REGEXP)

The NAME is a string, naming the proof assistant.
The SYMBOL is used to form the name of the mode for the
assistant, `SYMBOL-mode`, run when files with AUTOMODE-REGEXP
are visited.  SYMBOL is also used to form the name of the
directory and elisp file for the mode, which will be
 
    <proof-directory-home>/SYMBOL/SYMBOL.el

where `<proof-directory-home>/' is the value of the
variable proof-directory-home."
  :type '(repeat (list symbol string string))
  :group 'proof-internal)


;; Directories

(defcustom proof-internal-home-directory
  ;; FIXME: make sure compiling does not evaluate next expression.
  (or (getenv "PROOFGENERAL_HOME") 
      (let ((curdir 
	     (or
	      (and load-in-progress (file-name-directory load-file-name))
	      (file-name-directory (buffer-file-name)))))
	(file-name-directory (substring curdir 0 -1))))
  "*Directory where Proof General is installed. Ends with slash.
Default value taken from environment variable PROOFGENERAL_HOME if set, 
otherwise based on where the file proof-site was loaded from.
You can use customize to set this variable."
  :type 'directory
  :group 'proof-internal)

(defcustom proof-internal-images-directory
  (concat proof-internal-home-directory "images/")
    "*Where Proof General image files are installed. Ends with slash."
  :type 'directory
  :group 'proof-internal)

(defcustom proof-internal-info-directory
  (concat proof-internal-home-directory "doc/")
  "*Where Proof General Info files are installed."
  :type 'directory
  :group 'proof-internal)

;; Add the info directory to the end of Emacs Info path if need be.
;; It's easier to do this after Info has loaded because of the
;; complicated way the Info-directory-list is set.

(eval-after-load
 "info"
 '(or (member proof-internal-info-directory Info-directory-list)
     (progn
       (setq Info-directory-list
	     (cons proof-internal-info-directory
		   Info-directory-list))
       ;; Clear cache of info dir
       (setq Info-dir-contents nil))))


;; Might be nicer to have a boolean for each supported assistant.
(defcustom proof-assistants
  (mapcar (lambda (astnt) (car astnt))
	  proof-internal-assistant-table)
  (concat
   "*Choice of proof assitants to use with Proof General.
A list of symbols chosen from:" 
   (apply 'concat (mapcar (lambda (astnt) 
			    (concat " '" (symbol-name (car astnt))))
			  proof-internal-assistant-table)) 
".\nEach proof assistant defines its own instance of Proof General,
providing session control, script management, etc.  Proof General
will be started automatically for the assistants chosen here.
To avoid accidently invoking a proof assistant you don't have,
only select the proof assistants you (or your site) may need.
NOTE: to change proof assistant, you must start a new Emacs session.")
  :type (cons 'set 
	      (mapcar (lambda (astnt)
			(list 'const ':tag (car (cdr astnt)) (car astnt)))
		      proof-internal-assistant-table))
  :group 'proof)

;; Extend load path for the generic files.
(let ((proof-lisp-path
       (concat proof-internal-home-directory "generic/")))
  (or (member proof-lisp-path load-path)
      (setq load-path
	    (cons proof-lisp-path load-path))))

;; Now add auto-loads and load-path elements to support the 
;; proof assistants selected, and define a stub 
(let ((assistants proof-assistants) assistant)
  (while assistants
    (let*  
	((assistant (car assistants))
	 (nameregexp 
	  (or 
	   (cdr-safe 
	    (assoc assistant
		   proof-internal-assistant-table))
	   (error "proof-site: symbol " (symbol-name assistant) 
		  "is not in proof-internal-assistant-table")))
	 (assistant-name (car nameregexp))
	 (regexp	 (car (cdr nameregexp)))
	 (sname		 (symbol-name assistant))
	 ;; NB: File name for each prover is the same as its symbol name!
	 (elisp-file   sname)
	 ;; NB: Dir name for each prover is the same as its symbol name!
	 (elisp-dir    sname)
	 ;; NB: Mode name for each prover is <symbol name>-mode!
	 (proofgen-mode  (intern (concat sname "-mode")))
	 ;; NB: Customization group for each prover is its l.c.'d name!
	 (cusgrp	 (intern (downcase assistant-name)))

	 ;; Stub to do some automatic initialization and load
	 ;; the specific code.
	 (mode-stub
	   `(lambda ()
	      ,(concat
		 "Major mode for editing scripts for proof assistant "
		 assistant-name
		 ".\nThis is a stub which loads the real function.")
	      (interactive)
	      ;; Make a customization group for this assistant
	      (defgroup ,cusgrp nil
		,(concat "Customization of " assistant-name
			 " specific settings for Proof General.")
		:group 'proof)
	      ;; Set the proof-assistant configuration variable
	      (setq proof-assistant ,assistant-name)
	      ;; Extend the load path, load the real mode and invoke it.
	      (setq load-path 
		    (cons (concat proof-internal-home-directory ,elisp-dir "/")
			  load-path))
	      (load-library ,elisp-file)
	      (,proofgen-mode))))

      (setq auto-mode-alist 
	    (cons (cons regexp proofgen-mode) auto-mode-alist))

      (fset proofgen-mode mode-stub)
      
      (setq assistants (cdr assistants))
      )))

;; WARNING: do not edit below here 
;; (the next constant is set automatically)
(defconst proof-version "Proof General, Version 2.0pre981020 released by da,tms. Email proofgen@dcs.ed.ac.uk."
 "Version string for Proof General.")

(provide 'proof-site)


		 
  


      

