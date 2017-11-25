;;; macrostep-test.el --- tests for macrostep.el

;; Copyright (C) 2014-2015 Jon Oddie <j.j.oddie@gmail.com>

;; This file is NOT part of GNU Emacs.

;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see `http://www.gnu.org/licenses/'.


(eval-and-compile
  (require 'ert nil t)
  (require 'ert "lib/ert"))
(require 'rx)
(require 'macrostep)
(require 'macrostep-c)


;;;; Conveniences for defining tests

(defmacro macrostep-with-text (object &rest forms)
  (declare (indent 1)
           (debug (&rest form)))
  `(with-temp-buffer
     (emacs-lisp-mode)
     (let ((print-level nil)
           (print-length nil)
           (standard-output (current-buffer)))
       (save-excursion
         (print ,object))
       ,@forms)))

(defun macrostep-goto (text &optional from-point-min)
  (when from-point-min (goto-char (point-min)))
  (let ((search-spaces-regexp "[[:space:]\n]+"))
    (re-search-forward (regexp-quote text))
    (goto-char (match-beginning 0))))

(defmacro macrostep-should-expand (form expansion &optional leave-expanded-p)
  `(save-excursion
     (goto-char (point-min))
     (let ((print-level nil)
           (print-length nil))
       (search-forward (prin1-to-string ,form))
       (goto-char (match-beginning 0))
       (unwind-protect
            (progn
              (macrostep-expand)
              (should
               (equal (read (current-buffer))
                      ,expansion)))
	 (unless ,leave-expanded-p
	   (macrostep-collapse-all))))))


;;;; Tests
(ert-deftest macrostep-expand-defmacro ()
  (defmacro macrostep-dummy-macro (&rest args)
    `(expansion of ,@args))
  (macrostep-with-text
   '(progn
     (first body form)
     (second body form)
     (macrostep-dummy-macro (first (argument)) second (third argument))
     (remaining body forms))
   (macrostep-should-expand
    '(macrostep-dummy-macro (first (argument)) second (third argument))
    '(expansion of (first (argument)) second (third argument)))))

(ert-deftest macrostep-expand-and-collapse ()
  (dolist (expander
            (list
             (lambda (sexp _env) sexp)
             (lambda (sexp _env) `(progn ,sexp ,sexp))
             (lambda (sexp _env) `(long
                              (complicated
                               (expansion of ,sexp () ())
                               (with trailing forms))))))
    (let ((macrostep-expand-1-function expander)
          (macrostep-macro-form-p-function
           (lambda (&rest _) t)))
      (macrostep-with-text
          '(progn
            (first form)
            (second form)
            (third (nested form)))
        (macrostep-goto "(first ")
        (let ((original-text (buffer-string)))
          (dotimes (i 10)
            (dotimes (j i)
              (macrostep-expand))
            (dotimes (j i)
              (macrostep-collapse))
            (should (null macrostep-overlays))
            (should (string= (buffer-string)
                             original-text))))))))

(ert-deftest macrostep-expand-macrolet ()
  (macrostep-with-text
      '(cl-macrolet
        ((test (&rest args) `(expansion of ,@args)))
        (first body form)
        (second body form)
        (test (strawberry pie) and (apple pie))
        (final body form))
    (macrostep-should-expand
     '(test (strawberry pie) and (apple pie))
     '(expansion of (strawberry pie) and (apple pie)))))

(ert-deftest macrostep-expand-macrolet-2 ()
  (macrostep-with-text
      ;; Taken from org-notify.el.
      '(cl-macrolet ((get (k) `(plist-get list ,k))
                  (pr (k v) `(setq result (plist-put result ,k ,v))))
        (let* ((list (nth 1 heading))      (notify (or (get :notify) "default"))
               (deadline (org-notify-convert-deadline (get :deadline)))
               (heading (get :raw-value))
               result)
          (when (and (eq (get :todo-type) 'todo) heading deadline)
            (pr :heading heading)     (pr :notify (intern notify))
            (pr :begin (get :begin))
            (pr :file (nth org-notify-parse-file (org-agenda-files 'unrestricted)))
            (pr :timestamp deadline)  (pr :uid (md5 (concat heading deadline)))
            (pr :deadline (- (org-time-string-to-seconds deadline)
                             (org-float-time))))
          result))
    (macrostep-should-expand
     '(pr :heading heading)
     '(setq result (plist-put result :heading heading)))
    (macrostep-should-expand
     '(pr :notify (intern notify))
     '(setq result (plist-put result :notify (intern notify))))
    (macrostep-should-expand
     '(pr :begin (get :begin))
     '(setq result (plist-put result :begin (get :begin))))
    (macrostep-should-expand
     '(get :begin)
     '(plist-get list :begin))))

(ert-deftest macrostep-expand-cl-macrolet ()
  (macrostep-with-text
      ;; Taken from slime.el.
      '(cl-macrolet ((fontify (face string)
                      `(slime-inspector-fontify ,face ,string)))
        (slime-propertize-region
         (list 'slime-part-number id
          'mouse-face 'highlight
          'face 'slime-inspector-value-face)
         (insert title))
        (while (eq (char-before) ?\n)
          (backward-delete-char 1))
        (insert "\n" (fontify label "--------------------") "\n")
        (save-excursion
          (slime-inspector-insert-content content))
        (when point
          (cl-check-type point cons)
          (ignore-errors
            (goto-char (point-min))
            (forward-line (1- (car point)))
            (move-to-column (cdr point)))))
    (macrostep-should-expand
     '(fontify label "--------------------")
     '(slime-inspector-fontify label "--------------------"))))

(ert-deftest macrostep-expand-shadowed-macrolet ()
  (macrostep-with-text
      '(cl-macrolet
        ((test-macro (&rest forms) (cons 'shadowed forms))
         (test-macro (&rest forms) (cons 'outer-definition forms)))
        (test-macro first (call))
        (cl-macrolet
            ((test-macro (&rest forms) (cons 'inner-definition forms)))
          (test-macro (second (call)))))
    (macrostep-should-expand
     '(test-macro first (call))
     '(outer-definition first (call)))
    (macrostep-should-expand
     '(test-macro (second (call)))
     '(inner-definition (second (call))))))

(ert-deftest macrostep-environment-at-point ()
  (macrostep-with-text
      ;; Taken from org-notify.el.
      '(cl-macrolet ((get (k) `(plist-get list ,k))
                  (pr (k v) `(setq result (plist-put result ,k ,v))))
        (body forms))
    (search-forward "(body")
    (let ((env (macrostep-environment-at-point)))
      (should (assq 'get env))
      (should (assq 'pr env))
      (should (functionp (cdr (assq 'get env))))
      (should (functionp (cdr (assq 'pr env))))
      (should
       (equal
        (apply (cdr (assq 'pr env)) '(:heading heading))
        '(setq result (plist-put result :heading heading))))
      (should
       (equal
        (apply (cdr (assq 'get env)) '(:begin))
        '(plist-get list :begin))))))

(ert-deftest macrostep-environment-at-point-2 ()
  (defmacro macrostep-with-dummy (&rest body)
    `(cl-macrolet ((dummy (&rest forms) `(expansion of ,@forms)))
       ,@body))
  (macrostep-with-text
      '(macrostep-with-dummy
        (body)
        (forms)
        (cl-loop for i from 6 to 10
         do (something)))
    (macrostep-goto "(macrostep-with-dummy" t)
    (should (null (macrostep-environment-at-point)))

    (dolist (place (list "(body)" "dy)" "(forms)" "rms)"
                         "(something)"))
      (macrostep-goto place)
      (let* ((env (macrostep-environment-at-point))
             (dummy-defn (cdr (assq 'dummy env))))
        (should dummy-defn)
        (should (functionp dummy-defn))
        (should (equal
                 (funcall dummy-defn 'lorem 'ipsum)
                 `(expansion of lorem ipsum)))))))

(ert-deftest macrostep-print-sexp ()
  (cl-macrolet ((should-print (form string)
                  `(should (equal
                            (with-temp-buffer
                              (macrostep-print-sexp ,form)
                              (buffer-string))
                            ,string))))
    (should-print nil "nil")
    (should-print 'symbol "symbol")
    (should-print '(single-element-list) "(single-element-list)")
    (should-print '(two-element list) "(two-element list)")
    (should-print '(three element list) "(three element list)")
    (should-print '(dotted . list) "(dotted . list)")
    (should-print '(four element dotted . list) "(four element dotted . list)")
    (should-print '(nested (list (elements))) "(nested (list (elements)))")
    (should-print '((deeply (nested)) (list (elements)))
                  "((deeply (nested)) (list (elements)))")
    (should-print '(quote fishes) "'fishes")
    (should-print '`(backquoted form) "`(backquoted form)")
    (should-print '`(backquoted (form) ,with ,@splices)
                  "`(backquoted (form) ,with ,@splices)")))

(ert-deftest macrostep-pp-macrolet-environment ()
  (with-temp-buffer
    (emacs-lisp-mode)
    (macrostep-pp
     '(cl-macrolet ((some-macro (&rest forms) (cons 'progn forms)))
	(some-macro with (arguments))
	(intervening body forms)
	(some-macro with (more) (arguments)))
     nil)
    (cl-labels ((search (text)
                (macrostep-goto text t)
                ;; Leave point on the head of the form
                (forward-char)))
      ;; The occurrence of "(some-macro" in the binding list should
      ;; not be fontified as a macro form
      (search "(some-macro (&rest")
      (should-not
       (eq (get-char-property (point) 'font-lock-face)
           'macrostep-macro-face))

      ;; However, the two occurrences in the body of the macrolet should be.
      (search "(some-macro with (arguments)")
      (should
       (eq (get-char-property (point) 'font-lock-face)
           'macrostep-macro-face))

      (search "(some-macro with (more)")
      (should
       (eq (get-char-property (point) 'font-lock-face)
           'macrostep-macro-face)))))

(ert-deftest macrostep-expand-macro-defined-macros ()
  (defmacro with-local-dummy-macro (&rest body)
    `(cl-macrolet ((dummy (&rest args) `(expansion (of) ,@args)))
       ,@body))
  (macrostep-with-text
      '(with-local-dummy-macro
        (dummy form (one))
        (dummy (form two)))
    (macrostep-should-expand
     '(dummy form (one))
     '(expansion (of) form (one)))
    (macrostep-should-expand
     '(dummy (form two))
     '(expansion (of) (form two)))))

(ert-deftest macrostep-expand-in-separate-buffer ()
  (defmacro macrostep-dummy-macro (&rest args)
    `(expansion of ,@args))
  (let ((macrostep-expand-in-separate-buffer t))
    (macrostep-with-text
        '(progn
          (first form)
          (second form)
          (macrostep-dummy-macro (some (arguments)))
          (final form))
      (let ((original-buffer (current-buffer)))
        (search-forward "(macrostep-dummy-macro")
        (macrostep-expand)
        (should (not (equal (current-buffer) original-buffer)))
        (should macrostep-expansion-buffer)
        (should (equal (read (copy-marker (point)))
                       '(expansion of (some (arguments)))))))))

(ert-deftest macrostep-expand-macrolet-in-separate-buffer ()
  (let ((macrostep-expand-in-separate-buffer t))
    (macrostep-with-text
        '(cl-macrolet
          ((dummy-macro-1 (&rest args)
            `(dummy-macro-2 ,@args))
           (dummy-macro-2 (&rest args)
            `(expansion of ,@args)))
          (dummy-macro-1 (some (arguments))))
      (let ((original-buffer (current-buffer)))
        (macrostep-goto "(dummy-macro-1 (some")

        (macrostep-expand)
        (should (not (equal (current-buffer) original-buffer)))
        (should macrostep-expansion-buffer)
        (should (equal (read (copy-marker (point)))
                       '(dummy-macro-2 (some (arguments)))))

        (macrostep-expand)
        (should (equal (read (copy-marker (point)))
                       '(expansion of (some (arguments)))))

        (macrostep-collapse)
        (should (equal (read (copy-marker (point)))
                       '(dummy-macro-2 (some (arguments)))))))))

(ert-deftest macrostep-expand-compiler-macros ()
  "Test that compiler-macros are expanded"
  ;; definitions
  (defun macrostep-dummy-function (&rest args)
    args)
  (cl-define-compiler-macro macrostep-dummy-function (&rest args)
    `(compile-time expansion of ,@args))

  (macrostep-with-text
      '(progn
        (first body form)
        (macrostep-dummy-function first second third)
        (remaining body forms))
    (macrostep-should-expand
     '(macrostep-dummy-function first second third)
     '(compile-time expansion of first second third))))

(ert-deftest macrostep-fontify-compiler-macros ()
  "Test that compiler-macros are fontified in macro-expansions"
  ;; definitions
  (defmacro macrostep-dummy-macro (&rest args)
    `(expansion including (macrostep-dummy-function ,@args)))
  (defun macrostep-dummy-function (&rest args)
    args)
  (cl-define-compiler-macro macrostep-dummy-4 (&rest args)
    `(compile-time expansion of ,@args))

  (macrostep-with-text
      '(progn
        (first body form)
        (second body form)
        (macrostep-dummy-macro first second third)
        (remaining body forms))
    (macrostep-should-expand
     '(macrostep-dummy-macro first second third)
     '(expansion including (macrostep-dummy-function first second third))
     t)
    (macrostep-goto "(macrostep-dummy-function")
    (should
     (eq (get-char-property (1+ (point)) 'font-lock-face)
	 'macrostep-compiler-macro-face))
    
    (macrostep-should-expand
     '(macrostep-dummy-function first second third)
     '(compile-time expansion of first second third))))


;;;; Tests for C macro expansion

(defun macrostep-lax-looking-at (string)
  (let* ((string-sans-whitespace
          (replace-regexp-in-string (rx (one-or-more whitespace)) "" string))
         (regexp
          (cl-loop
           for char across string-sans-whitespace
           concat (rx-to-string char t)
           concat "[[:space:]]*")))
    (looking-at regexp)))

(defmacro macrostep-lax-should-expand (string)
  `(progn
     (macrostep-expand)
     (should (macrostep-lax-looking-at ,string))
     (macrostep-collapse)))

(ert-deftest macrostep-expand-c-macros ()
  (with-temp-buffer
    (insert
     ;; A random example adapted from Emacs's src/lisp.h.
     "
#define eassert(cond) ((void) (false && (cond))) /* Check COND compiles.  */
#define lisp_h_XLI(o) (o)
#define lisp_h_XUNTAG(a, type) ((void *) (intptr_t) (XLI (a) - (type)))
#define XLI(o) lisp_h_XLI (o)
#define XUNTAG(a, type) lisp_h_XUNTAG (a, type)

INLINE struct Lisp_String *
XSTRING (Lisp_Object a)
{
  eassert (STRINGP (a));
  return XUNTAG (a, Lisp_String);
}")
    (c-mode)

     ;; Test macro-expansion with point at the beginning of the macro
    (macrostep-goto "eassert (STRINGP (a))" t)
    (macrostep-lax-should-expand
     "((void) (false && (STRINGP (a))))")

    ;; Test with point inside a nested macro call: result should be
    ;; the same, since point will move up before the outermost macro
    (macrostep-goto "STRINGP")
    (macrostep-lax-should-expand
     "((void) (false && (STRINGP (a))))")

    ;; Test with point in the middle of a symbol
    (macrostep-goto "XUNTAG (a, Lisp_String)" t)
    (forward-char 3)
    (macrostep-lax-should-expand
     "((void *) (intptr_t) ((a) - (  Lisp_String)))")

    ;; Test with point at symbol-end
    (macrostep-goto "XUNTAG (a, Lisp_String)" t)
    (forward-sexp)
    (macrostep-lax-should-expand
     "((void *) (intptr_t) ((a) - (  Lisp_String)))")))



(when noninteractive
  (load-file (expand-file-name "macrostep.el"
                               (file-name-directory load-file-name)))
  (let ((stats (ert-run-tests-batch "^macrostep")))
        (if noninteractive
            (kill-emacs (ert-stats-completed-unexpected stats)))))
