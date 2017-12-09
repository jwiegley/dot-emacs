;;; Package definition file for eval-in-repl
;;
;; This has been created because it is a multi-file package.
;; Only dash.el and paredit.el are required for all installation.
;; Other dependencies are use-specific, so configure referring to:
;; https://github.com/kaz-yos/eval-in-repl/
;;
;; (define-package NAME-STRING VERSION-STRING &optional DOCSTRING
;; REQUIREMENTS &rest EXTRA-PROPERTIES)
;;
;; Define a new package.
;; NAME-STRING is the name of the package, as a string.
;; VERSION-STRING is the version of the package, as a string.
;; DOCSTRING is a short description of the package, a string.
;; REQUIREMENTS is a list of dependencies on other packages.
;;  Each requirement is of the form (OTHER-PACKAGE OTHER-VERSION),
;;  where OTHER-VERSION is a string.
;;
(define-package
  ;; NAME-STRING
  "eval-in-repl"
  ;; VERSION-STRING
  "%VERSION%"
  ;; DOCSTRING (Shown as Summary in package.el)
  "Consistent ESS-like eval interface for various REPLs"
  ;; REQUIREMENTS
  '((dash "0.0.0") (paredit "0.0.0") (ace-window "0.0.0"))
  ;; Shown as Homepage in package.el
  :url "https://github.com/kaz-yos/eval-in-repl/"
  ;; Shown as Keywords in package.el
  ;; :keywords ("utilities" "repl")
  )
