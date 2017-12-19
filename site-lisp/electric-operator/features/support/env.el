
;; Don't load old byte-compiled versions!
(setq load-prefer-newer t)

(require 'f)

(defvar electric-operator-support-path
  (f-dirname load-file-name))

(defvar electric-operator-features-path
  (f-parent electric-operator-support-path))

(defvar electric-operator-root-path
  (f-parent electric-operator-features-path))

(add-to-list 'load-path electric-operator-root-path)

(require 'electric-operator)
(require 'espuds)
(require 'ert)

(Setup
 ;; Before anything has run
 (load "rust-mode-autoloads")
 (load "ess-autoloads")
 (load "js2-mode-autoloads")
 (load "haskell-mode-autoloads")
 (load "julia-mode-autoloads")
 (load "php-mode-autoloads")

 ;; This fixes an issue in emacs 25.1 where the debugger would be invoked
 ;; incorrectly, breaking ert.
 (when (and (= emacs-major-version 25) (< emacs-minor-version 2))
   (require 'cl-preloaded)
   (setf (symbol-function 'cl--assertion-failed)
         (lambda (form &optional string sargs args)
           "This function has been modified by electric-operator to remove an incorrect manual call
to the debugger in emacs 25.1. The modified version should only be used for
running the espuds tests."
           (if string
               (apply #'error string (append sargs args))
             (signal 'cl-assertion-failed `(,form ,@sargs))))))
 )

(Before
 ;; Before each scenario is run
 )

(After
 ;; After each scenario is run
 )

(Teardown
 ;; After when everything has been run
 )
