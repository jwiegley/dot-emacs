;; pg-thymodes.el  Proof General "theory" modes.
;;
;; Copyright (C) 2002 LFCS Edinburgh. 
;; Author:   David Aspinall
;; License:  GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;; Functions for defining "theory" modes, i.e.  modes for
;; non-interactive proof assistant files which do not contain proof
;; scripts.
;;
;; STATUS: in progress, experimental; needs macro debugging.

(require 'proof)


;;;###autoload
(defmacro pg-defthymode (sym name &rest body)
  "Define a Proof General mode for theory files.
Mode name is SYM-mode, named NAMED.  BODY is the body of a setq and
can define a number of variables for the mode, viz:

  SYM-<font-lock-keywords>      (value for font-lock-keywords)
  SYM-<syntax-table-entries>	(list of pairs: used for modify-syntax-entry calls)
  SYM-<menu>			(menu for the mode, arg of easy-menu-define)
  SYM-<parent-mode>		(defaults to fundamental-mode)
  SYM-<filename-regexp>	        (regexp matching filenames for auto-mode-alist)

All of these settings are optional."
  (progn
    (eval `(setq ,@body))
    (let* 
	;; See what was defined
	((mode	      (intern (concat (symbol-name sym) "-mode")))
	 (parentmode  (pg-modesymval sym 'parent-mode 'fundamental-mode))
	 (flks	      (pg-modesymval sym 'font-lock-keywords))
	 (syntaxes    (pg-modesymval sym 'syntax-table-entries))
	 (menu	      (pg-modesymval sym 'menu))
	 (menusym     (pg-modesym sym 'menu))
	 (keymap      (pg-modesym mode 'map))
	 (fileregexp  (pg-modesymval sym 'filename-regexp)))
      ;; Set auto-mode-alist
      (if fileregexp
	  (setq auto-mode-alist
		(cons (cons fileregexp mode) auto-mode-alist)))
      ;; `(quote (list ,mode ,parentmode ,flks ,fileregexp)))))
      ;; Define the mode (also makes keymap)
      (eval
       `(define-derived-mode ,mode ,parentmode ,name
	  (interactive)
	  (pg-do-unless-null ,flks (setq font-lock-keywords ,flks))
	  (pg-do-unless-null ,syntaxes (mapcar 'modify-syntax-entry ,syntaxes))))
       ;; Define the menu (final value of macro to be evaluated)
       `(pg-do-unless-null ,menu
			   `(easy-menu-define 
			     ,menusym ,keymap
			     ,(concat "Menu for " 
				      (symbol-name mode)
				      " defined by `pg-defthymode'.")
			     ,menu)))))



;; Utilities

(defmacro pg-do-unless-null (val &rest body)
  `(if ,val
       (progn ,@body)))
    

(defun pg-symval (sym &optional other)
  "Return (symbol-value SYM) or nil/OTHER if SYM unbound."
  (if (boundp sym) 
      (symbol-value sym)
    other))

(defun pg-modesym (mode sym)
  "Return MODE-SYM."
  (intern (concat (symbol-name mode)  "-" (symbol-name sym))))

(defun pg-modesymval (mode sym &optional other)
  "Return value of symbol MODE-SYM or nil/OTHER if unbound."
  (let ((modesym  (pg-modesym mode sym)))
    (if (boundp modesym)
	(symbol-value modesym)
      other)))
  

  

(provide 'pg-thymodes)
;; pg-thymodes.el ends here.
