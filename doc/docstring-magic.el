;; doc/docstring-magic.el  -- hack for using texi-docstring-magic.
;;
;; Copyright (C) 1998 LFCS Edinburgh. 
;; Author: David Aspinall
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; Ensure that non-compiled versions of everything are loaded.
;;
;; $Id$
;;
(setq load-path
      (append '("../generic/") load-path))
(load "proof-site.el")
(require 'proof-autoloads)
(require 'proof-compat)
(require 'proof-utils)



;; FIXME: Loading several prover files at once is a bit of a problem
;; with new config mechanism.
;; Could abstract more code in proof-site.el to avoid duplication here.
(let ((assistants proof-assistants))	; assume not customized
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
	 (sname		 (symbol-name assistant))
	 (elisp-file   sname))
      (proof-ready-for-assistant assistant-name assistant)
      ;; Must load proof-config each time to define proof assistant
      ;; specific variables
      (setq features (delete 'proof-config features))
      (load "proof-config.el")
      (load-library elisp-file)
      (setq assistants (cdr assistants)))))

;; Now a fake proof assistant to document the automatically
;; specific variables
(proof-ready-for-assistant "PROOF ASSISTANT" 'PA)
(setq features (delete 'proof-config features))
(load "proof-config.el")


;; These next few are autoloaded usually
(load "thy-mode.el")
(load "proof-menu.el")
(load "proof-toolbar.el")

;; A couple of comint symbols are mentioned in the docs
(require 'comint)
;; Also completion
(require 'completion)

;; Set some symbols to make markup happen
(setq sml-mode 'markup-hack)
(setq func-menu 'markup-hack)

(load "texi-docstring-magic.el")