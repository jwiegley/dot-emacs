;; proof-system.el   Proof General functions for interfacing with proof system.
;;
;; Copyright (C) 2000 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; New in 3.2.  This file contains code for communicating settings 
;; maintained in Proof General with the underlying proof system,
;; and code for buiding useful prover specific commands.
;;

(require 'proof-config)


(defmacro proof-customize-toggle (var)
  "Make a function for toggling a boolean customize setting VAR.
The toggle function uses customize-set-variable to change the variable."
  `(lambda (arg)
     ,(concat "Toggle " (symbol-name var) ". With ARG, turn on iff ARG>0.
This function simply uses customize-set-variable to set the variable.
It was constructed with the macro proof-customize-toggle.")
     (interactive "P")
     (customize-set-variable 
      (quote ,var)
      (if (null arg) (not ,var)
	(> (prefix-numeric-value arg) 0)))))

;; FIXME: combine this with above, and remove messing calls in
;; proof-script.
(defmacro proof-deftoggle (var)
  "Define a function VAR-toggle for toggling a boolean customize setting VAR.
The toggle function uses customize-set-variable to change the variable."
  `(defun ,(intern (concat (symbol-name var) "-toggle")) (arg)
     ,(concat "Toggle " (symbol-name var) ". With ARG, turn on iff ARG>0.
This function simply uses customize-set-variable to set the variable.
It was constructed with the macro proof-deftoggle.")
     (interactive "P")
     (customize-set-variable 
      (quote ,var)
      (if (null arg) (not ,var)
	(> (prefix-numeric-value arg) 0)))))

(defmacro proof-defshortcut (fn string &optional key)
  "Define shortcut function FN to insert STRING, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is inserted using `proof-insert', which see.
KEY is added onto proof-assistant map."
  (if key
      (eval
       `(define-key proof-assistant-keymap ,key (quote ,fn))))
  `(defun ,fn ()
     "Shortcut command to insert a string."
     (interactive)
     (proof-insert ,string)))

  


;; End of proof-system.el
(provide 'proof-system)