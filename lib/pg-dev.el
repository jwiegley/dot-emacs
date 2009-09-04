;;; pg-dev.el --- Developer settings for Proof General
;;
;; Copyright (C) 2008 LFCS Edinburgh.
;; Author:      David Aspinall <David.Aspinall@ed.ac.uk> and others
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;; Commentary:
;; 
;; Some configuration of Emacs Lisp mode for developing PG, not needed
;; for ordinary users.
;;

;; Use checkdoc, eldoc, Flyspell:

;;; Code:
(add-hook 'emacs-lisp-mode-hook
	  '(lambda () (checkdoc-minor-mode 1)))

(add-hook 'emacs-lisp-mode-hook 'turn-on-eldoc-mode)

(add-hook 'emacs-lisp-mode-hook 'flyspell-prog-mode)


;; Configure indentation for our macros

(put 'proof-if-setting-configured 'lisp-indent-function 1)
(put 'proof-eval-when-ready-for-assistant 'lisp-indent-function 1)
(put 'proof-define-assistant-command 'lisp-indent-function 'defun)
(put 'proof-define-assistant-command-witharg 'lisp-indent-function 'defun)
(put 'defpgcustom 'lisp-indent-function 'defun)
(put 'proof-map-buffers 'lisp-indent-function 'defun)
(put 'proof-with-current-buffer-if-exists 'lisp-indent-function 'defun)

(defconst pg-dev-lisp-font-lock-keywords
  (list
   ;; FIXME: used to work but now not quite right, see font-lock.el to fix
   (concat "(\\(def\\(" ;; also proof-def
	   ;; Function like things
	   "^(\\(proof-def.*\\|defpg.*\\|defpa.*\\|.*asscustom\\)"
	   ;; Variable like things
    "\\([^ \t\n\(\)]*\\)"
    ;; Any whitespace and declared object.
    "[ \t'\(]*"
    "\\([^ \t\n\)]+\\)?")
   '(1 font-lock-keyword-face)
   '(8 (cond ((match-beginning 3) 'font-lock-variable-name-face)
	     ;; ((match-beginning 6) 'font-lock-type-face)
	     (t 'font-lock-function-name-face))
       nil t)))

;(add-hook 'emacs-lisp-mode-hook
;	  '(lambda ()
;	     (font-lock-add-keywords 'emacs-lisp-mode
;				     pg-dev-lisp-font-lock-keywords)))


;;;
;;; Autoloads (as used by "make autoloads")
;;;

(setq autoload-package-name "proof")
(setq generated-autoload-file "proof-autoloads.el")

;;;
;;; Unload utility (not wholly successful)
;;;

(defun unload-pg ()
  "Attempt to unload Proof General (for development use only)."
  (interactive)
  (mapcar
   (lambda (feat) (condition-case nil
		    (unload-feature feat 'force)
		    (error nil)))
   '(proof-splash pg-assoc pg-xml proof-depends proof-indent proof-site
     proof-shell proof-menu pg-pbrpm pg-pgip proof-script
     proof-autoloads pg-response pg-goals proof-toolbar
     proof-easy-config proof-config proof-mmm proof 
     proof-utils proof-syntax pg-user pg-custom
     proof-maths-menu proof-unicode-tokens
     pg-thymodes pg-autotest
     ;; 
     isar-syntax isar-find-theorems isar-unicode-tokens
     isar-autotest interface-setup isabelle-system isar isar-mmm
     isar-keywords
     ;;
     coq-abbrev coq-db coq-unicode-tokens coq-local-vars coq coq-syntax
     coq-indent coq-autotest)))

     

;;;
;;; Proling interesting packages
;;;

(defun profile-pg ()
  (interactive)
  (elp-instrument-package "proof-script")
  (elp-instrument-package "proof-shell")
  (elp-instrument-package "pg-response")
  (elp-instrument-package "comint")
  (elp-instrument-package "scomint")
  (elp-instrument-package "unicode-tokens")
  (elp-instrument-package "coq")
  (elp-instrument-package "isar"))  



(provide 'pg-dev)

;;; pg-dev.el ends here

