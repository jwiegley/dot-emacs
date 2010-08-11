;;; pg-pamacs.el --- Macros for per-proof assistant configuration
;;
;; Copyright (C) 2010  LFCS Edinburgh, David Aspinall.
;;
;; Author: David Aspinall <da@longitude>
;; Keywords: internal

;;; Commentary:
;;
;; Macros for defining per-assistant customization settings.
;;
;; This mechanism is an improved way to handle per-assistant settings.
;; Instead of declaring a variable "proof-assistant-web-page" and
;; duplicating it in the prover specific code to make the generic
;; setting, we automatically declare "isabelle-web-page",
;; "coq-web-page", etc, using these macros.
;;
;; The advantage of this is that people's save settings will work
;; properly, and that it will become more possible to use more than
;; one instance of PG at a time.  The disadvantage is that it is more
;; complicated, and less "object-oriented" than the previous approach.
;;
;; There are two mechanisms for accessing generic vars:
;;
;; (proof-ass name)  or (proof-assistant-name)
;;
;;
;; Developer's note: This code was previously in proof-utils.el.
;;

(require 'proof-site)			; proof-assitant-symbol
(require 'proof-compat)			; pg-custom-undeclare-variable
(require 'proof-autoloads)		; proof-debug

;;; Code:

(defmacro deflocal (var value &optional docstring)
  "Define a buffer local variable VAR with default value VALUE."
 `(progn
    (defvar ,var nil ,docstring)
    (make-variable-buffer-local (quote ,var))
    (setq-default ,var ,value)))

(deflocal proof-buffer-type nil
  "Symbol for the type of this buffer: 'script, 'shell, 'goals, or 'response.")


;;
;; Main macros
;;

(defmacro proof-ass-sym (sym)
  "Return the symbol for SYM for the current prover.  SYM not evaluated.
This macro should only be called once a specific prover is known."
  `(intern (concat (symbol-name proof-assistant-symbol) "-"
		   (symbol-name ',sym))))

(defmacro proof-ass-symv (sym)
  "Return the symbol for SYM for the current prover.  SYM evaluated.
This macro should only be invoked once a specific prover is engaged."
  `(intern (concat (symbol-name proof-assistant-symbol) "-"
		   (symbol-name ,sym))))

(defmacro proof-ass (sym)
  "Return the value for SYM for the current prover.
This macro should only be invoked once a specific prover is engaged."
  `(symbol-value (intern (concat (symbol-name proof-assistant-symbol) "-"
				 (symbol-name ',sym)))))

(defun proof-defpgcustom-fn (sym args)
  "Define a new customization variable <PA>-sym for current proof assistant.
Helper for macro `defpgcustom'."
  (let ((specific-var (proof-ass-symv sym))
	 (generic-var  (intern (concat "proof-assistant-" (symbol-name sym)))))
    (eval
     `(defcustom ,specific-var
       ,@args
       ;; We could grab :group from @args and prefix it.
       :group ,(quote proof-assistant-internals-cusgrp)))
    ;; For functions, we could simply use defalias.  Unfortunately there
    ;; is nothing similar for values, so we define a new set/get function.
    (eval
     `(defun ,generic-var (&optional newval)
	,(concat "Set or get value of " (symbol-name sym)
		 " for current proof assistant.
If NEWVAL is present, set the variable, otherwise return its current value.")
	(if newval
	    (setq ,specific-var newval)
	  ,specific-var)))))

(defun undefpgcustom (sym)
  (let ((specific-var (proof-ass-symv sym))
	(generic-var  (intern (concat "proof-assistant-" (symbol-name sym)))))
    (pg-custom-undeclare-variable specific-var)
    (fmakunbound generic-var)))

(defmacro defpgcustom (sym &rest args)
  "Define a new customization variable <PA>-SYM for the current proof assistant.
The function proof-assistant-<SYM> is also defined, which can be used in the
generic portion of Proof General to access the value for the current prover.
Arguments as for `defcustom', which see.

Usage: (defpgcustom SYM &rest ARGS)."
  `(proof-defpgcustom-fn (quote ,sym) (quote ,args)))



(defun proof-defpgdefault-fn (sym value)
  "Helper for `defpgdefault', which see.  SYM and VALUE are evaluated."
  ;; NB: we need this because nothing in customize library seems to do
  ;; the right thing.
  (let ((symbol  (proof-ass-symv sym)))
    (set-default symbol
		 (cond
		  ;; Use saved value if it's set
		  ((get symbol 'saved-value)
		   (car (get symbol 'saved-value)))
		  ;; Otherwise override old default with new one
		  (t
		   value)))))

(defmacro defpgdefault (sym value)
  "Set default for the proof assistant specific variable <PA>-SYM to VALUE.
This should be used in prover-specific code to alter the default values
for prover specific settings.

Usage: (defpgdefault SYM VALUE)"
    `(proof-defpgdefault-fn (quote ,sym) ,value))

;;
;; Make a function named for the current proof assistant.
;;
(defmacro defpgfun (name arglist &rest args)
  "Define function <PA>-SYM as for defun."
  `(defun ,(proof-ass-symv name) ,arglist
     ,@args))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Prover-assistant specific customizations
;; which are recorded in `proof-assistant-settings'
;;

;;; autoload for compiled version: used in macro proof-defpacustom
;;;###autoload
(defun proof-defpacustom-fn (name val args)
  "As for macro `defpacustom' but evaluating arguments."
  (let (newargs setting evalform type descr)
    (while args
      (cond
       ((eq (car args) :setting)
	(setq setting (cadr args))
	(setq args (cdr args)))
       ((eq (car args) :eval)
	(setq evalform (cadr args))
	(setq args (cdr args)))
       ((eq (car args) :pgipcmd)
	;; Construct a function which yields a PGIP string
	(setq setting `(lambda (x)
			  (pg-pgip-string-of-command (proof-assistant-format ,(cadr args) x))))
	(setq args (cdr args)))
       ((eq (car args) :pggroup)
	;; use the group as a prefix to the name, and set a pggroup property on it
	(setq name (intern (concat (downcase (cadr args)) ":" (symbol-name name))))
	(put name 'pggroup (cadr args))
	(setq args (cdr args)))
       ((eq (car args) :type)
	(setq type (cadr args))
	(setq args (cdr args))
	(setq newargs (cons type (cons :type newargs))))
       (t
	(setq newargs (cons (car args) newargs))))
      (setq args (cdr args)))
    (setq newargs (reverse newargs))
    (setq descr (car-safe newargs))
    (unless (and type
		  (or (eq (eval type) 'boolean)
		      (eq (eval type) 'integer)
		      (eq (eval type) 'string)))
      (error "defpacustom: missing :type keyword or wrong :type value"))
    ;; Debug message in case a defpacustom is repeated.
    ;; NB: this *may* happen dynamically, but shouldn't: if the
    ;; interface queries the prover for the settings it supports,
    ;; then the internal list should be cleared first.
    (if (assoc name proof-assistant-settings)
	(progn
	  (proof-debug "defpacustom: Proof assistant setting %s re-defined!"
		       name)
	  (undefpgcustom name)))
    (eval
     `(defpgcustom ,name ,val
	,@newargs
	:set 'proof-set-value
	:group 'proof-assistant-setting))
    (cond
     (evalform
      (eval
       `(defpgfun ,name ()
	  ,evalform)))
     (setting
      (eval
       `(defpgfun ,name ()
	  (proof-assistant-invisible-command-ifposs
	   (proof-assistant-settings-cmd (quote ,name)))))))
    (setq proof-assistant-settings
	  (cons (list name setting (eval type) descr)
		(assq-delete-all name proof-assistant-settings)))))

;;;###autoload
(defmacro defpacustom (name val &rest args)
  "Define a setting NAME for the current proof assitant, default VAL.
NAME can correspond to some internal setting, flag, etc, for the
proof assistant, in which case a :setting and :type value should be provided.
The :type of NAME should be one of 'integer, 'boolean, 'string.
The customization variable is automatically in group `proof-assistant-setting'.
The function `proof-assistant-format' is used to format VAL.
If NAME corresponds instead to a PG internal setting, then a form :eval to
evaluate can be provided instead."
  (eval-when-compile
    (if (boundp 'proof-assistant-symbol)
	;; declare variable to compiler to prevent warnings
	(eval `(defvar ,(proof-ass-sym name) nil "Dummy for compilation."))))
  `(proof-defpacustom-fn (quote ,name) (quote ,val) (quote ,args)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Evaluation once proof assistant is known
;;

(defmacro proof-eval-when-ready-for-assistant (&rest body)
  "Evaluate BODY once the proof assistant is determined (possibly now)."
  `(if (and (boundp 'proof-assistant-symbol) proof-assistant-symbol)
       (progn ,@body)
     (add-hook 'proof-ready-for-assistant-hook (lambda () ,@body))))



(provide 'pg-pamacs)
;;; pg-pamacs.el ends here
