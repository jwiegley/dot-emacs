;; proof-site.el -- Loading stubs for Proof General.
;;		    Configuration for site and choice of provers.
;;
;; Copyright (C) 1998-2003 LFCS Edinburgh. 
;; Author:      David Aspinall <David.Aspinall@ed.ac.uk>
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;; NB: Normally users do not need to edit this file.  Developers/installers
;; may want to adjust proof-assistant-table-default below.
;;
;; The environment variables PROOFGENERAL_HOME and PROOFGENERAL_ASSISTANTS 
;; can be set to affect load behaviour; see info documentation.
;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Master table of supported proof assistants. 
;;

(defconst proof-assistant-table-default
    '((isar   "Isabelle" "\\.thy$")
      (coq    "Coq"	 "\\.v$\\|\\.v8$\\|\\.v7$")
      (phox   "PhoX"	 "\\.phx$")
      (lego   "LEGO"	 "\\.l$")
      ;; (ccc    "CASL Consistency Checker"  "\\.ccc$")

      ;; For the demonstration instance of Proof General,
      ;; uncomment line below and set
      ;; export PROOFGENERAL_ASSISTANTS=demoisa. 
      ;; [NB: this is obsolete, only for old Isabelle files]a
      ;; (demoisa    "Isabelle Demo"	"\\.ML$")
      
      ;; The following provers are not fully supported, and have only
      ;; preliminary support written (please help to improve them!)
      
      ;; To use HOL, uncomment the line below.  It's disabled
      ;; by default because of clash with SML mode (same for .ML above).
      ;; (hol98	"HOL"		"\\.sml$")
      
      ;; (acl2	"ACL2"		"\\.acl2$")
      ;; (twelf	"Twelf"		"\\.elf$")
      (plastic	"Plastic"	"\\.lf$")
      ;; (lclam    "Lambda-CLAM"   "\\.lcm$")
      ;; (pgshell	"PG-Shell"	"\\.pgsh$")
      )
    "Default value for `proof-assistant-table', which see.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; PG version
;;

(eval-and-compile
;; WARNING: do not edit next line (constant is edited in Makefile.devel)
  (defconst proof-general-version "Proof General Version 3.7. Released by da on Thu 31 Jan 2008."
    "Version string identifying Proof General release."))

(defconst proof-general-short-version 
  (eval-when-compile
    (progn
      (string-match "Version \\([^ ]+\\)\\." proof-general-version)
      (match-string 1 proof-general-version))))

(defconst proof-general-version-year "2008")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Top-level customization groups
;;

(defgroup proof-general nil
  "Customization of Proof General."
  :group 'applications
  :prefix "proof-")

(defgroup proof-general-internals nil
  "Customization of Proof General internals for proof assistant configuration."
  :group 'applications
  :group 'proof-general
  :prefix "proof-")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Directories. Set at load time so compiled files can be relocated.
;; Load path must be extended manually during compilation.
;;

(defun proof-home-directory-fn ()
  "Used to set proof-home-directory."
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
  "Directory where Proof General is installed.  Ends with slash.
Default value taken from environment variable `PROOFGENERAL_HOME' if set, 
otherwise based on where the file `proof-site.el' was loaded from.
You can use customize to set this variable."
  :type 'directory
  :group 'proof-general-internals)

(defcustom proof-images-directory
  (concat proof-home-directory "images/")
    "Where Proof General image files are installed.  Ends with slash."
  :type 'directory
  :group 'proof-general-internals)

(defcustom proof-info-directory
  (concat proof-home-directory "doc/")
  "Where Proof General Info files are installed.  Ends with slash."
  :type 'directory
  :group 'proof-general-internals)

;; Extend load path for the generic and library files.
(add-to-list 'load-path (concat proof-home-directory "generic/"))
(add-to-list 'load-path (concat proof-home-directory "lib/"))

;; Declare some global variables
(require 'pg-vars)

;; Add the info directory to the Info path
(if ;; NB: proof-info-directory is bogus in RPM distrib.
    (file-exists-p proof-info-directory)
    (if (and (boundp 'Info-directory-list) (consp Info-directory-list))
	;; Info is already initialized.  Update its variables.
	;; This probably never happens in Emacs, but does in XEmacs.
	(if (not (member proof-info-directory Info-directory-list))
	    (progn
	      (add-to-list 'Info-directory-list proof-info-directory)
	      (setq Info-dir-contents nil)))
      ;; Info is not yet initialized.  Change its default.
      ;; Emacs uses Info-default-directory-list but it's deprecated in XEmacs
      (add-to-list 'Info-default-directory-list proof-info-directory)))

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
    proof-assistant-table-default))
  "*Proof General's table of supported proof assistants.
This is copied from `proof-assistant-table-default' at load time,
removing any entries that do not have a corresponding directory
under `proof-home-directory'.

Each entry is a list of the form

    (SYMBOL NAME AUTOMODE-REGEXP)

The NAME is a string, naming the proof assistant.
The SYMBOL is used to form the name of the mode for the
assistant, `SYMBOL-mode', run when files with AUTOMODE-REGEXP
are visited.  SYMBOL is also used to form the name of the
directory and elisp file for the mode, which will be
 
    PROOF-HOME-DIRECTORY/SYMBOL/SYMBOL.el

where PROOF-HOME-DIRECTORY is the value of the
variable `proof-home-directory'."
  :type '(repeat (list symbol string string))
  :group 'proof-general-internals)


(defcustom proof-assistants nil
  (concat
   "*Choice of proof assistants to use with Proof General.
A list of symbols chosen from:" 
   (apply 'concat (mapcar (lambda (astnt) 
			    (concat " '" (symbol-name (car astnt))))
			  proof-assistant-table)) 
".\nIf nil, the default will be ALL available proof assistants.

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

(defun proof-ready-for-assistant (assistantsym &optional assistant-name)
  "Configure PG for symbol ASSISTANTSYM, name ASSISTANT-NAME.
If ASSISTANT-NAME is omitted, look up in `proof-assistant-table'."
  (let*
      ((sname		 (symbol-name assistantsym))
       (assistant-name   (or assistant-name
			     (car-safe 
			      (cdr-safe (assoc assistantsym
					       proof-assistant-table)))
			     sname))
       (cusgrp-rt	 
	;; Normalized a bit to remove spaces and funny characters
	;; FIXME UGLY compatibility hack  
	;; (can use cl macro `substitute' but want to avoid cl here)
	;; NOTE: GNU Emacs 22/XEmacs 21.5 both have replace-regexp-in-string
	;; PG 3.8: move version forward here.
	(if (fboundp 'replace-in-string) 
	    ;; XEmacs
	    (replace-in-string (downcase assistant-name) "/\\|[ \t]+" "-")
	  ;; GNU Emacs
	  (subst-char-in-string 
	   ?/ ?\- 
	   (subst-char-in-string ?\ ?\- (downcase assistant-name)))))
	;; END compatibility hack
       (cusgrp	      (intern cusgrp-rt))
       (cus-internals (intern (concat cusgrp-rt "-config")))
       (elisp-dir     sname)		; NB: dirname same as symbol name!
       (loadpath-elt  (concat proof-home-directory elisp-dir "/")))
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
       ;; define the per-prover settings which depend on above 
       (require 'pg-custom)
       (setq proof-mode-for-shell (proof-ass-sym shell-mode))
       (setq proof-mode-for-response (proof-ass-sym response-mode))
       (setq proof-mode-for-goals (proof-ass-sym goals-mode))
       (setq proof-mode-for-script (proof-ass-sym mode))
       ;; Extend the load path if necessary
       (if (not (member ,loadpath-elt load-path))
	   (setq load-path (cons ,loadpath-elt load-path)))
       ;; Run hooks for late initialisation
       (run-hooks 'proof-ready-for-assistant-hook)))))


;; Add auto-loads and load-path elements to support the 
;; proof assistants selected, and define stub major mode functions
(let ((assistants
       (or (mapcar 'intern (split-string (or (getenv "PROOFGENERAL_ASSISTANTS") "")))
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
	   (error "Symbol %s is not in proof-assistant-table (in proof-site)" 
		  (symbol-name assistant))))
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
		   ;; and mode function wasn't redefined, be silent.
		   (message 
		    (concat 
		     ,assistant-name 
		     " Proof General error: Proof General already in use for "
		     proof-assistant))))
	      (t
	       ;; prepare variables and load path
	       (proof-ready-for-assistant (quote ,assistant) ,assistant-name)
	       ;; load the real mode and invoke it. 
	       (load-library ,elisp-file)
	       (,proofgen-mode))))))
	
	(setq auto-mode-alist 
	      (cons (cons regexp proofgen-mode) auto-mode-alist))
	
	(fset proofgen-mode mode-stub)
	
	(setq assistants (cdr assistants)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Disable any other XEmacs x-symbol packages: we load ours manually
;;;

(if (and
     (featurep 'xemacs)
     (not (featurep 'x-symbol-hooks)) ;; unless already loaded
     (file-exists-p (concat proof-home-directory ;; or our version removed
			    "x-symbol/lisp/"))
     ;; proof-try-require: make robust against missing advice package
     (condition-case () (require 'advice) (file-error nil) (featurep 'advice)))
    (defadvice packages-new-autoloads (after ignore-other-x-symbols activate)
      (setq ad-return-value 
	    (delete-if (lambda (pkg)
			 (string-match "x-symbol" pkg))
		       ad-return-value))))

(provide 'proof-site)
;; proof-site.el ends here
