;; proof-site.el -- Loading stubs for Proof General.
;;		    Configuration for site and choice of provers.
;;
;; Copyright (C) 1998-2002 LFCS Edinburgh. 
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;; NB: Normally you will not need to edit this file.  
;;

(if (featurep 'proof-site)	
    nil					; don't load twice

(if (or  (not (boundp 'emacs-major-version))
	 (< emacs-major-version 20))
    (error "Proof General is not compatible with Emacs %s" emacs-version))

(defgroup proof-general nil
  "Customization of Proof General."
  :group 'external
  :group 'processes
  :prefix "proof-")


;; This customization group gathers together
;; the internals of Proof General which control
;; configuration to different proof assistants.
;; This is for development purposes rather than
;; user-level customization, so this group does
;; not belong to 'proof-general (or any other group).
(defgroup proof-general-internals nil
  "Customization of Proof General internals."
  :prefix "proof-")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Directories
;;
(defun proof-home-directory-fn ()
  "Used to set proof-home-directory"
  (let ((s (getenv  "PROOFGENERAL_HOME")))
    (if s
	(if (string-match "/$" s) s (concat s "/"))
      (let ((curdir 
	     (or
	      (and load-in-progress (file-name-directory load-file-name))
	      (file-name-directory (buffer-file-name)))))
	(file-name-directory (substring curdir 0 -1))))))

(defcustom proof-home-directory
  (proof-home-directory-fn)
  "Directory where Proof General is installed. Ends with slash.
Default value taken from environment variable `PROOFGENERAL_HOME' if set, 
otherwise based on where the file `proof-site.el' was loaded from.
You can use customize to set this variable."
  :type 'directory
  :group 'proof-general-internals)

(defcustom proof-images-directory
  (concat proof-home-directory "images/")
    "Where Proof General image files are installed. Ends with slash."
  :type 'directory
  :group 'proof-general-internals)

(defcustom proof-info-directory
  (concat proof-home-directory "doc/")
  "Where Proof General Info files are installed. Ends with slash."
  :type 'directory
  :group 'proof-general-internals)

;; Add the info directory to the end of Emacs Info path if need be.
(if (and (boundp 'Info-directory-list) (consp Info-directory-list))
   ;; Info is already initialized.  Update its variables.
   ;; This probably never happens.  -stef
   (if (not (member proof-info-directory Info-directory-list))
      (progn
        (setq Info-directory-list
              (cons proof-info-directory Info-directory-list))
        (setq Info-dir-contents nil)))
  ;; Info is not yet initialized.  Change its default.
  (if (not (member proof-info-directory Info-default-directory-list))
      (setq Info-default-directory-list
	    (cons proof-info-directory Info-default-directory-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Master table of supported proof assistants. 
;;
(defcustom proof-assistant-table
  (apply 
   'append
   (mapcar
   ;; Discard entries whose directories have been removed.
    (lambda (dne)
      (let ((atts (file-attributes (concat proof-home-directory 
					   (symbol-name (car dne))))))
	(if (and atts (eq 't (car atts)))
	    (list dne)
	  nil)))
   '(;; For demonstration instance of Proof General,
    ;; export PROOFGENERAL_ASSISTANTS=demoisa. 
    ;;
    ;; To use Isabelle/Isar instead of classic Isabelle,
    ;; export PROOFGENERAL_ASSISTANTS=isar
    ;;
    (demoisa    "Isabelle Demo"	"\\.ML$")
    (isa        "Isabelle"	"\\.ML$\\|\\.thy$")
    (isar       "Isabelle/Isar" "\\.thy$")
    (lego	"LEGO"		"\\.l$")
    (coq	"Coq"		"\\.v$")
    (phox	"PhoX"		"\\.phx$")
    ;; The following provers are not fully supported, 
    ;; and have only preliminary support written 
    ;; (please volunteer to improve them!)
    (hol98	"HOL"		"\\.sml$")
    (acl2	"ACL2"		"\\.acl2$")
    (twelf	"Twelf"		"\\.elf$")
    ;; The following provers have experimental support, WIP
    (plastic	"Plastic"	"\\.lf$")
    (lclam      "Lambda-CLAM"   "\\.lcm$")
    ;; Next line for testing only
    ;; (pgip	"PGIP/Isa"	"\\.ML$\\|\\.thy$")
    )))
  "*Proof General's table of supported proof assistants.
Extend this table to add a new proof assistant.
Each entry is a list of the form

    (SYMBOL NAME AUTOMODE-REGEXP)

The NAME is a string, naming the proof assistant.
The SYMBOL is used to form the name of the mode for the
assistant, `SYMBOL-mode', run when files with AUTOMODE-REGEXP
are visited.  SYMBOL is also used to form the name of the
directory and elisp file for the mode, which will be
 
    PROOF-HOME-DIRECTORY/SYMBOL/SYMBOL.el

where `PROOF-HOME-DIRECTORY' is the value of the
variable proof-home-directory."
  :type '(repeat (list symbol string string))
  :group 'proof-general-internals)





;; A utility function.  Is there an alternative?
(defun proof-string-to-list (s separator) 
  "Return the list of words in S separated by SEPARATOR.
If S is nil, return empty list."
  (if s
      (let ((end-of-word-occurence (string-match (concat separator "+") s)))
	(if (not end-of-word-occurence)
	    (if (string= s "") 
		nil
	      (list s))
	  (cons (substring s 0 end-of-word-occurence) 
		(proof-string-to-list 
		 (substring s
			    (string-match (concat "[^" separator "]")
					  s end-of-word-occurence)) 
		 separator))))))

(defcustom proof-assistants nil
  (concat
   "*Choice of proof assistants to use with Proof General.
A list of symbols chosen from:" 
   (apply 'concat (mapcar (lambda (astnt) 
			    (concat " '" (symbol-name (car astnt))))
			  proof-assistant-table)) 
".\nIf nil, the default will be ALL proof assistants.

Each proof assistant defines its own instance of Proof General,
providing session control, script management, etc.  Proof General
will be started automatically for the assistants chosen here.
To avoid accidently invoking a proof assistant you don't have,
only select the proof assistants you (or your site) may need.

You can select which proof assistants you want by setting this
variable before `proof-site.el' is loaded, or by setting
the environment variable `PROOFGENERAL_ASSISTANTS' to the
symbols you want, for example \"lego isa\".  Or you can
edit the file `proof-site.el' itself.

Note: to change proof assistant, you must start a new Emacs session.")
  :type (cons 'set 
	      (mapcar (lambda (astnt)
			(list 'const ':tag (car (cdr astnt)) (car astnt)))
		      proof-assistant-table))
  :group 'proof-general)


;; Extend load path for the generic files.
(let ((proof-lisp-path
       (concat proof-home-directory "generic/")))
  (or (member proof-lisp-path load-path)
      (setq load-path
	    (cons proof-lisp-path load-path))))

;; During compilation from the Makefile, generic is on the load path.
;; Add all of the prover directories.
;; FIXME: this doesn't work quite right.  We want to test
;; whether we are running during a compilation.  How?
; (eval-when-compile
;  (dolist (assistant proof-assistant-table)
;    (let ((path (concat proof-home-directory
;			(concat (symbol-name (car assistant)) "/"))))
;      (or (member path load-path)
;	  (setq load-path
;		(cons path load-path))))))

(defun proof-ready-for-assistant (assistant-name assistantsym)
  "Configure PG for ASSISTANT-NAME, symbol ASSISTANTSYM."
  (let*
      ((sname		 (symbol-name assistantsym))
       (cusgrp-rt	 
	;; Normalized a bit to remove spaces and funny characters
	;; FIXME UGLY compatibility hack  
	;; (can use cl macro `substitute' but want to avoid cl here)
	(if (fboundp 'replace-in-string) 
	    ;; XEmacs
	    (replace-in-string (downcase assistant-name) "/\\|[ \t]+" "-")
	  ;; FSF
	  (subst-char-in-string 
	   ?/ ?\- 
	   (subst-char-in-string ?\ ?\- (downcase assistant-name)))))
	;; END compatibility hack
       (cusgrp	 (intern cusgrp-rt))
       (cus-internals  (intern (concat cusgrp-rt "-config")))
       ;; NB: Dir name for each prover is the same as its symbol name!
       (elisp-dir    sname)
       (loadpath-elt (concat proof-home-directory elisp-dir "/")))
    (eval `(progn
       ;; Make a customization group for this assistant
       (defgroup ,cusgrp nil
	 ,(concat "Customization of user options for " assistant-name
		  " Proof General.")
	 :group 'proof-general)
       ;; And another one for internals
       (defgroup ,cus-internals nil
	 ,(concat "Customization of internal settings for "
		  assistant-name " configuration.")
	 :group 'proof-general-internals
	 :prefix ,(concat sname "-"))
    
       ;; Set the proof-assistant configuration variables
       ;; NB: tempting to use customize-set-variable: wrong!
       ;; Here we treat customize as extended docs for these
       ;; variables.
       (setq proof-assistant-cusgrp (quote ,cusgrp))
       (setq proof-assistant-internals-cusgrp (quote ,cus-internals))
       (setq proof-assistant ,assistant-name)
       (setq proof-assistant-symbol (quote ,assistantsym))
       ;; Extend the load path if necessary
       (if (not (member ,loadpath-elt load-path))
	   (setq load-path (cons ,loadpath-elt load-path)))))))

;; Now add auto-loads and load-path elements to support the 
;; proof assistants selected, and define a stub 
(let ((assistants
       (or (mapcar 'intern
		   (proof-string-to-list
		    (getenv "PROOFGENERAL_ASSISTANTS") " "))
	   proof-assistants
	   (mapcar (lambda (astnt) (car astnt)) proof-assistant-table))))
  (while assistants
    (let*  
	((assistant (car assistants))	; compiler bogus warning here
	 (nameregexp			
	  (or 
	   (cdr-safe 
	    (assoc assistant
		   proof-assistant-table))
	   (error "proof-site: symbol " (symbol-name assistant) 
		  "is not in proof-assistant-table")))
	 (assistant-name (car nameregexp))
	 (regexp	 (car (cdr nameregexp)))
	 (sname		 (symbol-name assistant))
	 ;; NB: File name for each prover is the same as its symbol name!
	 (elisp-file   sname)
	 ;; NB: Mode name for each prover is <symbol name>-mode!
	 (proofgen-mode  (intern (concat sname "-mode")))
	 ;; NB: Customization group for each prover is its l.c.'d name!

	 ;; Stub to do some automatic initialization and load
	 ;; the specific code.
	 (mode-stub
	   `(lambda ()
	      ,(concat
		 "Major mode for editing scripts for proof assistant "
		 assistant-name
		 ".\nThis is a stub which loads the real function.")
	      (interactive)
	      ;; Give a message and stop loading if proof-assistant is
	      ;; already set: things go wrong if proof general is
	      ;; loaded for more than one prover.
	      (cond
	       ((and (boundp 'proof-assistant)
		     (not (string-equal proof-assistant "")))
		(or (string-equal proof-assistant ,assistant-name)
		    ;; If Proof General was partially loaded last time
		    ;; and mode function wasn't redefined,  be silent.
		    (message 
		     (concat 
		      ,assistant-name 
		      " Proof General error: Proof General already in use for "
		      proof-assistant))))
	       (t
		;; prepare variables and load path
		(proof-ready-for-assistant ,assistant-name 
					   (quote ,assistant))
		;; load the real mode and invoke it. 
		(load-library ,elisp-file)
		(,proofgen-mode))))))

      (setq auto-mode-alist 
	    (cons (cons regexp proofgen-mode) auto-mode-alist))

      (fset proofgen-mode mode-stub)
      
      (setq assistants (cdr assistants))
      )))

;; WARNING: do not edit below here 
;; (the next constant is set automatically, also its form is
;;  relied upon in proof-config.el, for proof-splash-contents)
(defconst proof-general-version "Proof General Version 3.4pre020827. Released by da."
 "Version string identifying Proof General release.")

;; Now define a few autoloads and basic variables.

;; 1.8.01: add a dummy package-provide command so proof-autoloads
;; is compatible with FSF Emacs.  Needed for next provide
;; (otherwise would be in proof-compat.el).
(or (fboundp 'package-provide)
    (defun package-provide (name &rest attributes)
      "Dummy version of XEmacs function for FSF compatibility."))


(require 'proof-autoloads)		; autoloaded functions

(defcustom proof-assistant-cusgrp nil
  "Symbol for the customization group of the user options for the proof assistant.
Do not change this variable! It is set automatically by the mode 
stub defined in proof-site, from the name given in 
proof-assistant-table."
  :type 'sexp
  :group 'prover-config)

(defcustom proof-assistant-internals-cusgrp nil
  "Symbol for the customization group of the PG internal settings proof assistant.
Do not change this variable! It is set automatically by the mode 
stub defined in proof-site, from the name given in
proof-assistant-table."
  :type 'sexp
  :group 'prover-config)

(defcustom proof-assistant ""
  "Name of the proof assistant Proof General is using.
Do not change this variable! It is set automatically by the mode 
stub defined in proof-site, from the name given in 
proof-assistant-table."
  :type 'string
  :group 'prover-config)

(defcustom proof-assistant-symbol nil
  "Symbol for the proof assistant Proof General is using.
Used for automatic configuration based on standard variable names.
Settings will be found by looking for names beginning with this
symbol as a prefix.
Do not change this variable! It is set automatically by the mode 
stub defined in proof-site, from the symbols given in 
proof-assistant-table."
  :type 'sexp
  :group 'prover-config)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Architecture flags
;;;

(eval-and-compile
(defvar proof-running-on-XEmacs (string-match "XEmacs" emacs-version)
  "Non-nil if Proof General is running on XEmacs.")
(defvar proof-running-on-Emacs21 (and (not proof-running-on-XEmacs)
				      (>= emacs-major-version 21))
  "Non-nil if Proof General is running on GNU Emacs 21 or later.")
;; rough test for XEmacs on win32, anyone know about GNU Emacs on win32?
(defvar proof-running-on-win32 (fboundp 'win32-long-file-name)
  "Non-nil if Proof General is running on a win32 system."))

(provide 'proof-site))
;; proof-site.el ends here
