;;; proof.el --- Proof General theorem prover interface.

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira

;; License:   GPL (GNU GENERAL PUBLIC LICENSE)

;; Keywords: languages

;;; Commentary:
;;
;; This file loads Proof General.  It is required by the
;; individual prover modes.  Loading order of PG is:
;;
;; 1. proof-site (variables, autoloads & stubs for mode functions)
;; 2. stub <PA>-mode function sets proof-assistant-symbol and related variables
;; 3. prover-dependent variables defined in pg-custom
;; 4. stub explicitly loads <PA>/<PA>.el and execute real mode function
;; 5. <PA>.el requires this file, rest of PG loaded here
;; 6. further modules loaded by autoloads/prover-specific requires.
;;
;;
;;; Code:

(require 'proof-site)			; site/prover config, global vars, autoloads

(unless (or noninteractive (bound-and-true-p byte-compile-current-file))
  (proof-splash-message))		; welcome the user now.

(require 'proof-compat)			; Emacs and OS compatibility
(require 'proof-utils)			; utilities
(require 'proof-config)			; configuration variables
(require 'proof-auxmodes)		; auxmode functions
(require 'proof-script)			; script mode
(require 'proof-tree)			; proof tree visualization with prooftree
(require 'proof-shell)			; shell mode

(provide 'proof)
;;; proof.el ends here
