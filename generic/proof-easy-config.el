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

(require 'proof)

(unless (fboundp 'defvaralias)
  (error "proof-easy-config only works for XEmacs, sorry!"))

(autoload 'custom-group-members "cus-edit")


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
(defvaralias 'proof-mode-for-goals 'proof-mode-for-pbp)

(defun proof-easy-config-define-derived-modes ()
  (dolist (modedef proof-easy-config-derived-modes-table)
    (let* ((prefixsym (nth 0 modedef))
	   (suffixnm  (nth 1 modedef))
	   (parent    (nth 2 modedef))
	   (body      (nthcdr 3 modedef))
	   (modert    (concat (symbol-name proof-assistant-symbol)
			      "-" prefixsym))
	   ; config function for mode -- don't need it with global settings.
	   ; (modecfgfn (intern (concat modert "-config")))
	   (hyphen    (if (string-equal prefixsym "") "" "-"))
	   (mode      (intern (concat modert hyphen "mode")))
	   (modename  (concat proof-assistant " " suffixnm))
	   (varname   (intern (concat "proof-mode-for-" suffixnm))))

      (eval
       `(define-derived-mode ,mode ,parent ,modename nil ,@body))

      ;; Set proof-mode-for-script, etc.  NB: at top-level rather
      ;; than in function body.  Then we don't need to set
      ;; proof-pre-shell-start-hook.
      (set varname mode))))

(defun proof-easy-config-define-customs ()
  "Define a -prog-name customization setting."
  (let* ((pn-def  (symbol-name proof-assistant-symbol))
	 (pn	 (intern (concat pn-def "-prog-name"))))
    `(defcustom ,pn ,pn-def
       ,(concat "*Name of program to run " proof-assistant)
       :type 'string
       :group ,proof-assistant-symbol)))

(defun proof-easy-config-check-setup (sym name)
  "A number of simple checks."
  (cond
   ((or 
     (and (boundp 'proof-assistant) proof-assistant 
	  (not (equal proof-assistant ""))
	  (not (equal proof-assistant name)))
     (and (boundp 'proof-assistant-symbol) proof-assistant-symbol
	  (not (eq proof-assistant-symbol sym))))
    (error "proof-easy-config: Proof General is already in use for a different prover!"))
   (t
    ;; Setting these here is nice for testing: no need to get
    ;; proof-assistants-table right first.
    (customize-set-variable 'proof-assistant name)
    (customize-set-variable 'proof-assistant-symbol sym))))

(defmacro proof-easy-config (sym name &rest body)
  "Configure Proof General for proof-assistant using BODY as a setq body."
  `(progn
     (proof-easy-config-check-setup ,sym ,name)
     (proof-easy-config-make-var-aliases ,sym 'prover-config)
     (proof-easy-config-define-customs)
     (setq
      ,@body)
     (proof-easy-config-define-derived-modes)))
  
;; 
(provide 'proof-easy-config)

