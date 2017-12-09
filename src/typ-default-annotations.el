;;; -*- lexical-binding: t -*-

(eval-when-compile
  (require 'cl-lib))

(defun typ--default-annotations-load ()
  "Unconditionally load default annotations."
  ;; NOTE: if you add additional definitions here,
  ;;       please do not forget to add tests for it.
  ;;
  ;; Special case for nil.
  (typ-annotate nil :nil)
  ;; Fill `integer' functions.
  (dolist (fn '(lsh
                char-syntax
                point
                length))
    (typ-annotate fn :integer))
  ;; Fill `float' functions.
  (dolist (fn '(float))
    (typ-annotate fn :float))
  ;; Fill `number' functions.
  (dolist (fn '(string-to-number))
    (typ-annotate fn :number))
  ;; Fill `string' functions.
  (dolist (fn '(int-to-string
                number-to-string
                char-to-string
                concat
                symbol-name))
    (typ-annotate fn :string))
  ;; Fill `symbol' functions.
  (dolist (fn '(intern))
    (typ-annotate fn :symbol))
  ;; Fill `boolean' functions.
  (dolist (fn '(not
                symbolp
                stringp
                consp
                listp))
    (typ-annotate fn :boolean))
  ;; Fill mixed type functions.
  (cl-flet
      ;; Common function handlers defined inside this `flet'.
      ((num-arith
        (args)
        ;; - `:float' if at least 1 arg is float
        ;; - `:integer' if all arguments are integers
        ;; - `:number' otherwise
        (let ((found-float nil)
              (all-ints t))
          (while (and args
                      (not found-float))
            (let ((type (typ-infer (car args))))
              (if (eq :float type)
                  (setq found-float t)
                (unless (eq :integer type)
                  (setq all-ints nil))
                (setq args (cdr args)))))
          (cond (found-float :float)
                (all-ints :integer)
                (t :number))))
       )
    ;; `quote' forces quoted context for `typ-infer' resolution.
    (typ-annotate-mixed
     'quote
     (pcase-lambda (`(,arg)) (typ-infer arg t)))
    (typ-annotate-mixed
     'elt
     (pcase-lambda (`(,seq . _)) (typ-infer-elt seq)))
    (typ-annotate-mixed
     'aref
     (pcase-lambda (`(,arr . _))
       (let ((type (typ-infer arr)))
         (if (typ-array? type)
             (typ-elt type)
           nil))))
    (typ-annotate-mixed
     'nth
     (pcase-lambda (`(_ ,lst))
       (pcase (typ-infer lst)
         (`(:list . ,type) type))))
    ;; Arith functions.
    (typ-annotate-mixed '+ #'num-arith)
    (typ-annotate-mixed '- #'num-arith)
    (typ-annotate-mixed '* #'num-arith)
    (typ-annotate-mixed '/ #'num-arith)))
