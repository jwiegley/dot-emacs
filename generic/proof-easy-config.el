;; proof-easy-config.el    Easy configuration for Proof General
;;
;; Copyright (C) 1999  David Aspinall / LFCS.
;; Author:     David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer: Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; Work in progress.
;; 
;; XEmacs only at the moment (uses defvaralias)
;;
;; Future version might copy settings instead.  Consider how best to
;; interface with customization mechanism so a new prover can be
;; configured by editing inside custom buffers.
;;

(unless (fboundp 'defvaralias)
  (error "proof-easy-config only works for XEmacs, sorry!"))


(defun proof-easy-config-make-var-aliases (sym group)
  "Make variable aliases for custom GROUP, with new prefix SYM."
  (let ((vars	  (custom-group-members group nil))
	(prefix  (length
		  (or (get 'custom-prefix group) ; fails sometimes, why?
		      "proof-")))	; common prefix
	(newpref (concat (symbol-name sym) "-")))
    (dolist (cusmem vars)
      (cond ((member 'custom-group cusmem)
	     ;; recurse on subgroups
	     (proof-easy-config-make-var-aliases sym (car cusmem)))
	    ((member 'custom-variable cusmem)
	     (let* ((thisone   (car cusmem))
		    (base	(substring (symbol-name thisone) prefix))
		    (alias	(intern (concat newpref base))))
	       (defvaralias alias thisone)))))))

(defvar proof-easy-config-derived-modes-table
  '((""         "script" proof-mode (proof-config-done))
    ("shell"    "shell"  proof-shell-mode (proof-shell-config-done))
    ("response" "resp"   proof-response-mode (proof-response-config-done))
    ("goals"	"goals"   pbp-mode (proof-goals-config-done)))
  "A list of (PREFIXSYM SUFFIXNAME PARENT MODEBODY) for derived modes.")

;; FIXME: Non-uniformity in current code
(defvaralias proof-mode-for-goals proof-mode-for-pbp)

(defun proof-easy-config-define-derived-modes ()
  (dolist (modedef proof-easy-config-derived-modes-table)
    (let* ((prefixsym (nth 1 modedef))
	   (suffixnm  (nth 2 modedef))
	   (parent    (nth 3 modedef))
	   (body      (nthcdr 4 modedef))
	   (modert    (concat proof-assistant-symbol "-" prefixsym))
	   (modecfgfn (intern (concat modert "config")))
	   (hyphen    (if (string-equal prefixsym "") "" "-"))
	   (mode      (intern (concat modert hyphen "mode")))
	   (fullbody  (cons (list modecfgfn) body))
	   (modename  (concat proof-assistant " " suffixnm))
	   (varname   (intern (concat "proof-mode-for-" suffixnm))))

      `(define-derived-mode ,mode ,parent ,modename nil ,@fullbody)

      ;; A hook into the mode body, before proof-config-done is
      ;; called.  Probably unnecessary: the generic mode hook
      ;; functions would insert code in the same place.

      `(defun ,modecfgfn () 
	 ,(concat "Special configuration for " modert "mode.
You can redefine this function, currently it does nothing."))

      ;; Set proof-mode-for-script, etc.  NB: at top-level rather
      ;; than in function body.  Then we don't need to set
      ;; proof-pre-shell-start-hook.
      `(setq ,varname ,mode))))

(defun proof-easy-config-define-customs ()
  "Define a -prog-name customization setting."
  (let ((pn-def  (symbol-name proof-assistant-symbol))
	(pn	 (intern (concat pn-def "-prog-name"))))
    `(defcustom ,pn ,pn-def
       ,(concat "*Name of program to run " proof-assistant)
       :type 'string
       :group ,proof-assistant-symbol)
    ;; An alias which shadows ordinary proof-prog-name
    (defvaralias 'proof-prog-name pn)))

(defmacro proof-easy-config (body)
  "Configure Proof General for proof-assistant using settings in BODY."
  `(progn
     (proof-easy-config-make-var-aliases proof-assistant-symbol 'prover-config)
     (proof-easy-config-define-customs)
     ,@body
     (proof-easy-config-define-derived-modes)))
  
;; 
(provide 'proof-easy-config)

