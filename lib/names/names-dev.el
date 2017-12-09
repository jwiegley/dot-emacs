;;; names-dev.el --- Developer Functions to facilitate use of names.el with your package.

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Prefix: names
;; Separator: -

;;; Commentary:
;;
;; This package has some convenient functions for developers working
;; with names.el.
;; This package is installed along with names.el, but to use its
;; features you must require it explicitly:
;;
;;     (require 'names-dev)

;;; License:
;;
;; This file is part of GNU Emacs.
;;
;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:

(require 'names)
(require 'elisp-mode nil t)
(require 'lisp-mode nil t)


;;; ---------------------------------------------------------------
;;; Developer Utility Functions
(defmacro names-compare-forms (name form-a form-b)
  "Test if (namespace NAME FORM-A) is the same as FORM-B."
  (declare (indent (lambda (&rest x) 0))
           (debug (symbolp sexp form)))
  `(equal
    (macroexpand-all '(define-namespace ,name :global :verbose ,form-a))
    (macroexpand-all ',form-b)))

(defmacro names-compare-forms-assert (name form-a form-b)
  "Assert if (namespace NAME FORM-A) is the same as FORM-B."
  (declare (indent (lambda (&rest x) 0))
           (debug (symbolp sexp form)))
  (cl-assert
   (names-compare-forms name form-a form-b)
    t))

(defmacro names-print (name &rest forms)
  "Return the expanded results of (namespace NAME :global :verbose FORMS).
Ideal for determining why a specific form isn't being parsed
correctly. You may need to set `eval-expression-print-level' and
`eval-expression-print-length' to nil in order to see your full
expansion."
  (declare (indent (lambda (&rest x) 0)) (debug 0))
  `(define-namespace ,name :global :verbose ,@forms))

(defvar names-font-lock
  '(("^:autoload\\_>" 0 'font-lock-warning-face prepend)
    ("(\\(\\_<define-namespace\\_>\\)[\t \n]+\\([^\t \n]+\\)"
     (1 'font-lock-keyword-face)
     (2 'font-lock-variable-name-face))))

(when (boundp 'lisp-el-font-lock-keywords-2)
  (setq lisp-el-font-lock-keywords-2
        (append names-font-lock
                lisp-el-font-lock-keywords-2)))


;;; The backbone
(defun names--looking-at-namespace ()
  "Non-nil if point is at a `define-namespace' form or an alias to it."
  (when (looking-at "(\\_<")
    (save-excursion
      (forward-char 1)
      (ignore-errors
        (equal (indirect-function (intern (thing-at-point 'symbol)))
               (indirect-function 'define-namespace))))))

(defun names--generate-new-buffer (name &optional form)
  "Generate and return a new buffer.
NAME is current namespace name.
If FORM is provided, also try to use it to decide an informative
buffer name."
  (get-buffer-create
   (concat
    " *names "
    (format "%s %s"
            (or (car-safe form) (random 10000))
            (or (car-safe (cdr-safe form)) (random 10000)))
    "*")))

(defmacro names--wrapped-in-namespace (command form &optional kill &rest body)
  "Call COMMAND, except in a namespace.
In a namespace, expand FORM in a separate buffer then execute
BODY. If BODY is nil, call COMMAND instead.
If KILL is non-nil, kill the temp buffer afterwards."
  (declare (indent defun)
           (debug (sexp form form body)))
  ;; Get the namespace, if we're in one.
  `(let ((evaled-form ,form)
         (invocation
          ',(if (commandp command t)
                `(call-interactively #',command)
              command))
         (entire-namespace
          (save-excursion
            (when (names--top-of-namespace)
              (cdr (read (current-buffer))))))
         b keylist spec name expanded-form)

     ;; If we're not in a namespace, call the regular `eval-defun'.
     (if (null entire-namespace)
         (eval invocation)
       ;; If we are, expand the function in a temp buffer
       (setq name (pop entire-namespace))
       (while (setq spec (names--next-keyword entire-namespace))
         (setq keylist (append keylist spec)))
       ;; Prepare the (possibly) temporary buffer.
       (setq b (names--generate-new-buffer name evaled-form))
       (unwind-protect
           (with-current-buffer b
             (cl-letf (((symbol-function #'message) #'ignore))
               (erase-buffer)
               (emacs-lisp-mode)
               ;; Print everything inside the `progn'.
               (mapc
                (lambda (it) (pp it (current-buffer)))
                (cdr
                 (setq expanded-form
                       (macroexpand
                        `(define-namespace ,name :global :clean-output ,@keylist ,evaled-form)))))
               (when (fboundp 'font-lock-ensure)
                 (font-lock-ensure)))
             ;; Return value
             ,@(or body '((eval invocation))))
         ;; Kill the buffer if we won't need it.
         (when (and ,kill (buffer-live-p b))
           (kill-buffer b))))))

(defun names--top-of-namespace ()
  "Move to the top of current namespace, and return non-nil.
If not inside a namespace, return nil and don't move point."
  (let ((top (save-excursion
               (beginning-of-defun)
               (ignore-errors
                 (backward-up-list))
               (when (names--looking-at-namespace)
                 (point)))))
    (when top
      (goto-char top)
      t)))

(defun names-eval-defun (edebug-it)
  "Identical to `eval-defun', except it works for forms inside namespaces.
Argument EDEBUG-IT is the same as `eval-defun', causes the form
to be edebugged."
  (interactive "P")
  (require 'font-lock) ; just in case
  (let ((form
         (save-excursion
           (end-of-defun)
           (beginning-of-defun)
           (read (current-buffer)))))
    (names--wrapped-in-namespace
      eval-defun form (null edebug-it))))


;;; eval-last-sexp
(defalias 'names--preceding-sexp-original
  (if (fboundp 'elisp--preceding-sexp)
      (symbol-function 'elisp--preceding-sexp)
    (symbol-function 'preceding-sexp)))

(defun names--preceding-sexp ()
  "Like `elisp--preceding-sexp', but expand namespaces."
  (names--wrapped-in-namespace
    (names--preceding-sexp-original) (names--preceding-sexp-original) t
    expanded-form))

(defun names-eval-last-sexp (eval-last-sexp-arg-internal)
  "Identical to `eval-last-sexp', except it works for forms inside namespaces.
Argument EVAL-LAST-SEXP-ARG-INTERNAL is the same as `eval-last-sexp'."
  (interactive "P")
  (cl-letf (((symbol-function 'elisp--preceding-sexp) #'names--preceding-sexp)
            ((symbol-function 'preceding-sexp) #'names--preceding-sexp))
    (eval-last-sexp eval-last-sexp-arg-internal)))

(defun names-eval-print-last-sexp (eval-last-sexp-arg-internal)
  "Identical to `eval-print-last-sexp', except it works for forms inside namespaces.
Argument EVAL-LAST-SEXP-ARG-INTERNAL is the same as `eval-print-last-sexp'."
  (interactive "P")
  (cl-letf (((symbol-function 'elisp--preceding-sexp) #'names--preceding-sexp)
            ((symbol-function 'preceding-sexp) #'names--preceding-sexp))
    (eval-print-last-sexp eval-last-sexp-arg-internal)))

;; (pp (symbol-function 'names--preceding-sexp-original) (current-buffer))

(defun names-pprint ()
  "Pretty-print an expansion of the namespace around point."
  (interactive)
  (save-excursion
    (when (names--top-of-namespace)
      (let ((ns (cdr (read (current-buffer)))))
        (pp-macroexpand-expression
         (macroexpand (cons 'names-print ns)))))))


;;; Find stuff
(require 'find-func nil t)
(defalias 'names--fboundp-original (symbol-function 'fboundp))
(defalias 'names--boundp-original (symbol-function 'boundp))
(defalias 'names--find-function-read-original (symbol-function 'find-function-read))
(defalias 'find-function-read 'names--find-function-read)

(defun names--find-function-read (&optional type)
  "Identical to `find-function-read', except it works inside namespaces."
  (let ((buf (current-buffer)))
    (names--wrapped-in-namespace
      (names--find-function-read-original type) nil t
      (set-buffer buf)
      (let ((names--name name))
        (cl-letf (((symbol-function 'fboundp) #'names--dev-fboundp)
                  ((symbol-function 'boundp) #'names--dev-boundp))
          (names--find-function-read-original type))))))

(defun names--dev-fboundp (sym)
  (or (names--fboundp-original sym)
      (names--fboundp-original (names--prepend sym))))
(defun names--dev-boundp (sym)
  (or (names--boundp-original sym)
      (names--boundp-original (names--prepend sym))))


;;; The keys
(eval-after-load 'lisp-mode
  '(let ((map emacs-lisp-mode-map))
     (define-key map [remap eval-defun] #'names-eval-defun)
     (define-key map [remap eval-last-sexp] #'names-eval-last-sexp)
     (define-key map [remap eval-print-last-sexp] #'names-eval-print-last-sexp)))

(provide 'names-dev)

;;; names-dev.el ends here
