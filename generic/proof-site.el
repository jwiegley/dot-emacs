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
;; One possible hack: changing prover in the proof-assistant setting
;; below could re-adjust load path and autoloads.

;; 
(defvar proof-general-version ""
  "Version string for Proof General.")

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

(defcustom proof-assistant
  'isa
  "*Choice of proof assitant to run generic mode with.
A symbol chosen from: 'lego 'coq 'isa
To change proof assistant, you must start a new Emacs session."
  :type '(choice (const :tag "Isabelle" isa)
		 (const :tag "LEGO" lego)
		 (const :tag "Coq" coq))
  :group 'proof)

;; Extend load path
(setq load-path
      (cons (concat proof-home "generic/")
	    (cons (concat proof-home (symbol-name proof-assistant) "/")
		  load-path)))


;; Add auto-loads to support the prover selected
(let* ((fileregexp (cond
		    ((eq proof-assistant 'coq)    "\\.v")
		    ((eq proof-assistant 'lego)   "\\.l$")
		    ((eq proof-assistant 'isa)    "\\.ML$")))
       (assistant   (symbol-name proof-assistant))
       (proof-mode  (intern (concat assistant "-mode"))))
      
  (setq auto-mode-alist 
	(cons (cons fileregexp proof-mode) auto-mode-alist))

  ;; NB: File name for each prover is the same as its symbol name!
  (autoload proof-mode assistant
    (concat
     "Major mode for editing scripts for proof assistant " assistant ".")
    t)
  )
  
(provide 'proof-site)


		 
  


      

