;;; proof-auxmodes.el --- Arrange for auxiliary modes to be loaded when required

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>

;; License:   GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Startup code from auxiliary modes are collected here, allowing late
;; loading of their main defining files and the possibility to disable them.
;;

;;; Code:

(require 'proof-utils)			; proof-ass, proof-eval...

;;
;; Maths menu
;;
(defun proof-maths-menu-support-available ()
  "A test to see whether maths-menu support is available.
The test loads optional prover-specific config in <foo>-maths-menu.el"
  (or (proof-try-require (proof-ass-sym maths-menu)) t))

(proof-eval-when-ready-for-assistant
    (if (and (proof-ass maths-menu-enable)
	     (proof-maths-menu-support-available))
	(proof-maths-menu-set-global t)))


;;
;; Unicode tokens
;;
(defun proof-unicode-tokens-support-available ()
  "A test to see whether unicode tokens support is available."
  ;; Requires prover-specific config in <foo>-unicode-tokens.el
  ;; Loaded before unicode-tokens.el to allow load-time config there
  (proof-try-require (proof-ass-sym unicode-tokens)))

(proof-eval-when-ready-for-assistant
    (if (and (proof-ass unicode-tokens-enable)
	     (proof-unicode-tokens-support-available))
	(proof-unicode-tokens-set-global t)))


(provide 'proof-auxmodes)

;;; proof-auxmodes.el ends here
