;;; lego-site.el  Site-specific Emacs support for LEGO
;;; Copyright (C) 1998 LFCS Edinburgh
;;; Author: Thomas Kleymann <T.Kleymann@ed.ac.uk>
;;; Maintainer: lego@dcs.ed.ac.uk

(let ((version (getenv "PROOFGENERAL")))
  (cond ((not version)		;default
	 (setq load-path
	       (cons "/usr/local/share/elisp/script-management" load-path))
	 (setq load-path
	       (cons "/usr/local/share/elisp/script-management/lego" load-path))
	 (setq auto-mode-alist (cons '("\\.l$" . lego-mode) auto-mode-alist))
	 (autoload 'lego-mode "lego" "Major mode for editing Lego proof scripts." t))
	((string= version "ancient") 
	 (setq load-path (cons "/usr/local/share/elisp/lego" load-path))
	 (setq auto-mode-alist (cons '("\\.l$" . lego-mode) auto-mode-alist))
	 (autoload 'lego-mode "lego" "Major mode for editing Lego proof scripts." t)
	 (autoload 'lego-shell "lego" "Inferior shell invoking lego." t))
	((string= version "latest")
	 (load-file "/usr/local/share/elisp/ProofGeneral/generic/proof-site.el"))))
	 

	 