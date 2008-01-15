;;; proof.el --- Proof General loader.  
;;
;; Copyright (C) 1998-2008 LFCS Edinburgh.
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;; Commentary:
;; 
;; This file loads Proof General.  It is required by the
;; individual prover modes.  Loading order of PG is:
;;
;; 1. proof-site (autoloads & stubs for mode functions)
;; 2. autoload of <PA>/<PA>.el by auto-mode-alist 
;; 3. <PA>.el requires this file
;; 4. rest of PG loaded here, inc proof-config/pg-custom
;; 5. further modules loaded by autoloads.
;; 
;;; Code:

(require 'proof-site)			; site/prover config, global vars
(require 'proof-autoloads)		; autoloaded functions
(require 'proof-compat)			; Emacs and OS compatibility
(require 'proof-utils)			; utilities
(require 'proof-config)			; configuration variables

(proof-splash-message)			; welcome the user now.

(provide 'proof)
;;; proof.el ends here
