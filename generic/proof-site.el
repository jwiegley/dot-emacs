;; proof-site.el --- Configuration for site and choice of prover.
;;
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Thomas Kleymann
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; FUTURE: in the future it might be nice to allow switching between
;; different proof assistants in the same session.  Presently, the
;; code will only allow one assistant to be chosen for the whole
;; session.

(or (featurep 'custom)
    ;; Quick hack to support defcustom for Emacs 19
    (defmacro defcustom (sym val doc &rest args)
      (defvar sym val doc))
    (defmacro group (sym mems doc &rest args)))

(defgroup proof nil
  "Customization of generic parameters for proof mode."
  :group 'external
  :group 'processes)

(defcustom proof-home
  (or (getenv "PROOF_HOME") "~/devel/lego/elisp/")
  "*Directory where proof mode is installed. Ends with slash.
Default value taken from PROOF_HOME, or use customize to set it."
  :type 'directory
  :group 'proof)

(defcustom proof-image-directory
  (concat proof-home "images/")
    "*Where proof mode image files are installed. Ends with slash."
  :type 'directory
  :group 'proof)

(defcustom proof-assistants
  '(isa lego coq)
  "*Choice of proof assitants to use with Proof General.
A list of symbol chosen from: 'lego 'coq 'isa
NB: To change proof assistant, you must start a new Emacs session."
  :type '(set (const :tag "Isabelle" isa)
	      (const :tag "LEGO" lego)
	      (const :tag "Coq" coq))
  :group 'proof)

;; Extend load path
(setq load-path
      (cons (concat proof-home "generic/") load-path))


;; Add auto-loads and load-path elements
;; to support the proof assistants selected
(let ((assistants proof-assistants) proof-assistant)
  (while assistants
    (let*  
	((proof-assistant (car assistants))
	 (fileregexp 
	  (cond ((eq proof-assistant 'coq)    "\\.v")
		((eq proof-assistant 'lego)   "\\.l$")
		((eq proof-assistant 'isa)    "\\.ML$|\\.thy$")))
	 (assistant-name   (symbol-name proof-assistant))
	 (proof-mode  (intern (concat assistant-name "-mode"))))
      (setq auto-mode-alist 
	    (cons (cons fileregexp proof-mode) auto-mode-alist))
      ;; NB: File name for each prover is the same as its symbol name!
      (autoload proof-mode assistant-name
	(concat
	 "Major mode for editing scripts for proof assistant " assistant-name ".")
	t)
      (setq load-path 
	    (cons
	     (concat proof-home (symbol-name proof-assistant) "/")
	     load-path))
      (setq assistants (cdr assistants))
      )))
  
;; WARNING: do not edit below here 
;; (the next constant is set automatically)
(defconst proof-general-version
 "Proof General, Version 2.0-pre980910 released by da,tms. Email lego@dcs.ed.ac.uk."
 "Version string for Proof General.")

(provide 'proof-site)


		 
  


      

