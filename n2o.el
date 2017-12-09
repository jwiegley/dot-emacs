;;; n2o.el --- extra Emacs Lisp optimizer -*- lexical-binding: t -*-

;; Author: Iskander Sharipov <quasilyte@gmail.com>
;; Keywords: lisp

;;; Commentary:

;; "n2o.el", or nitrous is standalone, independent Emacs Lisp optimizer
;; that can be installed into stock Emacs to improve
;; the performance of byte compiled code.
;; Once loaded and enabled (non-nil `n2o-enabled') it
;; transparently applies additional optimizations.
;;
;; The simplest way to inspect how it really works is to
;; look at the `disassemble' function output.
;; (let ((n2o-enabled t)) (disassemble '(lambda () (+ 2 x))))
;; vs
;; (let ((n2o-enabled nil)) (disassemble '(lambda () (+ 2 x))))
;; With `n2o':
;;   varref x
;;   add1
;;   add1
;; Without `n2o':
;;   constant 2
;;   varref x
;;   plus
;; Both snippets lead to the same result, but double `add1' does
;; not require to store "2" constant,
;; which reduces the constant vector size.

;;; Todo:

;; - Add tests.
;; - Add benchmarks.

;;; Code:

(require 'typ)

;; This call should not be unconditional, probably.
(typ-default-annotations-load)

(defcustom n2o-enabled t
  "Non-nil value enables additional byte compiler optimizations.

As an effect, produced byte code, hopefully, is faster,
at the cost of slightly slower compilation."
  :group 'bytecomp
  :type 'boolean)

(advice-add 'byte-compile-form :around #'n2o-advice-byte-compile-form)

(defun n2o-advice-byte-compile-form (compile &rest args)
  "Advice function that is designed to wrap `byte-compile-form' (COMPILE).
Does simple forwarding if `n2o-enabled' is nil,
otherwise it acts as additional optimizer that sits between
builtin high level source optimizer and
builtin low level byte code optimizer.

ARGS are normaly a list of `form' and `for-effect', but it may
be untrue if other advice functions are set."
  (if (not n2o-enabled)
      (apply compile args)
    (let* ((form (pop args))
           (for-effect (pop args)))
      (setq form (n2o--source-opt form for-effect))
      (n2o--emit-form compile form for-effect))))

(defun n2o--source-opt (form for-effect)
  "Try to return optimized version of FORM.
Performs tranformations on the source level only."
  (pcase form
    ;; Spare `2' constant without any speed loss.
    (`(+ ,x 2)
     `(1+ (1+ ,x)))
    (`(+ 2 ,x)
     `(1+ (1+ ,x)))
    (`(- ,x 2)
     `(1- (1- ,x)))
    (`(* ,x 2)
     `(+ ,x ,x))
    (`(* 2 ,x)
     `(+ ,x ,x))
    ;; Cdr-safe and car-safe.
    ;; TODO: the bound patterns should be recursive.
    (`(if (consp ,x) (car ,x) nil)
     `(car-safe ,x))
    (`(if (consp ,x) (car ,x) ,y)
     `(or (car-safe ,x) ,y))
    (`(if (consp ,x) (cdr ,x) nil)
     `(cdr-safe ,x))
    (`(if (consp ,x) (cdr ,x) ,y)
     `(or (cdr-safe ,x) ,y))
    (`(if (listp ,x) (car ,x) nil)
     `(car-safe ,x))
    (`(if (listp ,x) (cdr ,x) nil)
     `(cdr-safe ,x))
    ;; Replace forms with faster alternatives.
    (`(if (> ,x ,y) ,x ,y)
     `(max ,x ,y))
    (`(if (> ,x ,y) ,y ,x)
     `(min ,x ,y))
    (`(if (< ,x ,y) ,x ,y)
     `(min ,x ,y))
    (`(if (< ,x ,y) ,y ,x)
     `(max ,x ,y))
    (`(eq nil ,x)
     `(null ,x))
    (`(eq ,x nil)
     `(null ,x))
    ;; Inlining for some popular functions.
    (`(alist-get ,key ,alist)
     `(cdr (assq ,key ,alist)))
    (`(nth 2 ,list)
     `(car (cdr (cdr ,list))))
    ;; More complex rewrites.
    (`(assoc ,key ,alist)
     (n2o--rewrite-assoc form key alist))
    (`(lsh . ,_)
     (n2o--rewrite-lsh form))
    (`(mapcar . ,_)
     (n2o--rewrite-mapcar form for-effect))
    (`(format . ,_)
     (n2o--rewrite-format form))
    (`(eql ,x ,y)
     (n2o--rewrite-eql form x y))
    (`(= ,x ,y)
     (n2o--rewrite-= form x y))
    (`(/= ,x ,y)
     (n2o--rewrite-/= form x y))
    (`(zerop ,x)
     (n2o--rewrite-zerop form x))
    ;; Do not know how to optimize -- return `form' unchanged.
    (_ form)))

(defun n2o--rewrite-assoc (form key alist)
  (if (memq (typ-infer key) '(:integer :symbol))
      `(assq ,key ,alist)
    form))

(defun n2o--rewrite-lsh (form)
  ;; Replace left shift with multiplication.
  ;; VM has fast `mult' instruction, while `lsh' requires funcall.
  ;; Do not replace right shifts with division because it
  ;; may result in slower code.
  (let ((value (nth 1 form))
        (count (nth 2 form)))
    (if (and (typ-infer-integer? value)
             (integerp count)
             (> count 0))
        (let ((c (expt 2 count)))
          `(* ,value ,c))
      form)))

(defun n2o--rewrite-mapcar (form for-effect)
  (if for-effect
      (let ((fn (nth 1 form))
            (seq (nth 2 form)))
        ;; `mapc' should be used if evaluation result is ignored.
        `(mapc ,fn ,seq))
    form))

(defun n2o--rewrite-format (form)
  (pcase form
    (`(format "%d" ,x)
     `(number-to-string ,x))
    (`(format "%c" ,x)
     (if (typ-infer-number? x)
         `(char-to-string ,x)
       form))
    (`(format "%s" ,x)
     ;; TODO: may also be a good idea to check for `:symbol'
     ;;       and use `symbol-name'.
     (if (typ-infer-number? x)
         `(number-to-string ,x)
       ;; Could return `prin1-to-string', but it
       ;; requires some investigation whenever this is
       ;; valid or not.
       form))
  (_ form)))

(defun n2o--rewrite-eql (form x y)
  ;; `eql' is slower than `eq' and `equal'.
  ;; `eql' behaves like `equal' when first operand is float,
  ;; otherwise it calls `eq' under the hood.
  (let ((x-type (typ-infer x)))
    (if (and x-type
             (not (eq :float x-type)))
        `(eq ,x ,y)
      form)))

(defun n2o--rewrite-zerop (form x)
  (if (typ-infer-integer? x)
      `(eq ,x 0)
    form))

(defun n2o--rewrite-/= (form x y)
  ;; Same reasoning as in `=' vs `eq'.
  (if (and (typ-infer-integer? x)
           (typ-infer-integer? y))
      `(not (eq ,x ,y))
    form))

(defun n2o--rewrite-= (form x y)
  ;; For integers, `eq' is a valid and faster alternative.
  (if (and (typ-infer-integer? x)
           (typ-infer-integer? y))
      `(eq ,x ,y)
    form))

(defun n2o--emit-form (compile form for-effect)
  "With COMPILE as a fallback, emit optimized FORM.
Matches Lisp forms, outputs byte code.
FOR-EFFECT has the same meaning as in `byte-compile-form'."
  ;; Disable `discard' outputting for noreturn function calls.
  (when (and (listp form)
             (typ-noreturn? (car form)))
    (setq for-effect nil))
  (pcase form
    (`(while ,test . ,body)
     (n2o--emit-while test body))
    (_ (funcall compile form for-effect))))

(defun n2o--emit-while (test body)
  "Compiles (while TEST ...BODY) form.
Like `byte-compile-while', but outputs code that
does only 1 `goto' per iteration instead of 2.
Surprisingly, the speedup is not significant, but
can be measured (for large number of iterations)."
  (let ((cond-label (byte-compile-make-tag))
        (body-label (byte-compile-make-tag)))
    ;; Make a jump into condition check right away.
    ;; If condition is true, looping commences.
    ;; This kind of `while' compilation is very
    ;; popular among native code producing compilers.
    (byte-compile-out 'byte-goto cond-label)
    (byte-compile-out-tag body-label)
    (byte-compile-body body t)
    (byte-compile-out-tag cond-label)
    (byte-compile-form test)
    (byte-compile-out 'byte-goto-if-not-nil body-label)
    (setq byte-compile--for-effect nil)))

(provide 'n2o)

;;; n2o.el ends here
