;;; lego-site.el  Site-specific Emacs support for LEGO
;;; Copyright (C) 1998 LFCS Edinburgh
;;; Author: Thomas Kleymann <T.Kleymann@ed.ac.uk>
;;; Maintainer: lego@dcs.ed.ac.uk

(let ((version (getenv "PROOFGENERAL")))
  (cond ((string= version "")		;default
	 (setq load-path
	       (cons "/usr/local/share/elisp/script-management" load-path))
	 (setq load-path
	       (cons "/usr/local/share/elisp/script-management/lego" load-path))
	 (load "lego"))
	((string= version "ancient") 
	 (setq load-path (cons "/usr/local/share/elisp/lego" load-path))
	 (load "lego"))
	((string= version "latest")
	 (load-file "/usr/local/share/elisp/ProofGeneral/generic/proof-site.el"))))
	 

	 