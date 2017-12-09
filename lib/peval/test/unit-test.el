(require 'ert)
(require 'peval)

;; TODO: refactor this so we have an intact (peval--simplify ...)
;; when using it, so we can conveniently evaluate subforms interactively.
(defmacro should-partially-simplify (form bindings expected-result)
  (let ((result-sym (make-symbol "result")))
    `(let ((,result-sym (peval--simplify ,form ,bindings)))
       (should
        (not (peval-result-evaluated-p ,result-sym)))
       (should
        (equal (peval-result-value ,result-sym)
               ,expected-result)))))

(defmacro should-fully-simplify (form bindings expected-result)
  (let ((result-sym (make-symbol "result")))
    `(let ((,result-sym (peval--simplify ,form ,bindings)))
       (should
        (peval-result-evaluated-p ,result-sym))
       (should
        (equal (peval-result-value ,result-sym)
               ,expected-result)))))

(ert-deftest peval--cond ()
  ;; Simplify no arms.
  (should-partially-simplify
   '(cond
     (a (b))
     (c (d e) f))
   nil
   '(cond
     (a (b))
     (c (d e) f)))
  ;; Simplify some arms
  (should-partially-simplify
   '(cond
     (a (+ b 1))
     (c d)
     (e (foo)))
   '((b . 3) (c . 5))
   '(cond
     ;; We don't know if this clause will be evaluated, but we can
     ;; simplify its body.
     (a 4)
     ;; We know this clause is true, so we can discard later clauses.
     (5 d)))
  
  ;; Simplify cond entirely.
  (should-partially-simplify
   '(cond
     (a 1)
     (b c)
     (e (foo)))
   '((a . nil) (b . t))
   'c)
  ;; cond clause without body.
  (should-fully-simplify
   '(cond
     (a)
     (b))
   '((a . nil) (b . 123))
   123)
  ;; No clauses evaluate to t.
  (should-fully-simplify
   '(cond
     (a (foo))
     (b (bar)))
   '((a . nil) (b . nil))
   nil)
  ;; Single unknown clause could just be a when.
  (should-partially-simplify
   '(cond
     (a (foo) (x))
     (b (bar) (x))
     (c (baz) (x)))
   '((a . nil) (c . nil))
   '(when b (bar) (x)))
  ;; Single unknown clause without a body.
  (should-partially-simplify
   '(cond
     (a (foo) (x))
     (b)
     (c (baz) (x)))
   '((a . nil) (c . nil))
   'b))

(ert-deftest peval--progn ()
  (should-fully-simplify
   '(progn 1)
   nil
   1)
  (should-partially-simplify
   '(progn nil y)
   nil
   'y)
  (should-partially-simplify
   '(progn x nil y)
   nil
   '(progn x y)))

(ert-deftest peval--when ()
  ;; Falsy condition.
  (should-fully-simplify
   '(when nil x y)
   nil
   nil)
  ;; Truthy condition.
  (should-partially-simplify
   '(when t x y)
   nil
   '(progn x y))
  ;; Evaluating body.
  (should-partially-simplify
   '(when x y)
   '((y . 1))
   '(when x 1))
  ;; Regression test: we should only evaluate the body once.
  (should-partially-simplify
   '(when x y)
   '((y . (progn . b)))
   '(when x (progn . b))))

(ert-deftest peval--unless ()
  (should-partially-simplify
   '(unless nil x y)
   nil
   '(progn x y))
  (should-fully-simplify
   '(unless t x y)
   nil
   nil)
  (should-partially-simplify
   '(unless x y)
   '((y . 1))
   '(unless x 1))
  (should-partially-simplify
   '(unless x y z)
   '((z . 1))
   '(unless x y 1)))

(ert-deftest peval--known-fn-call ()
  "If we know we're calling a function, we should simplify its
arguments."
  ;; Function with side effects.
  (should-partially-simplify
   '(message x)
   '((x . 1))
   '(message 1))
  ;; Pure function.
  (should-fully-simplify
   '(+ x 2)
   '((x . 3))
   5))

(ert-deftest peval--unknown-fn-call ()
  "If we don't recognise the symbol, do nothing."
  (should-partially-simplify
   '(foo x)
   '((x . 1))
   '(foo x)))

(ert-deftest peval--setq-result ()
  "The result of a setq is the assigned value."
  ;; One assignment.
  (should-fully-simplify
   '(setq x (1+ 1))
   nil
   2)
  ;; Multiple assignments.
  (should-fully-simplify
   '(setq x (1+ 1) y (1+ 2) z (1+ 3))
   nil
   4))

(ert-deftest peval--setq-propagate ()
  "After evaluating a setq, we know the value of the variable.
We should update subsequent references."
  ;; Simplify to known value and propagate.
  (should-fully-simplify
   '(progn (setq x 1) x)
   nil
   1)
  ;; Don't propagate after a value becomes unknown.
  (should-partially-simplify
   '(progn (setq x (foo)) x)
   '((x . 1))
   '(progn (setq x (foo)) x))
  ;; Once a variable is unknown, we can't use it in later assignments.
  (should-partially-simplify
   '(setq x (foo) y x)
   '((x . 1))
   '(setq x (foo) y x)))

;; (ert-deftest peval--set ()
;;   "Correctly evaluate `set'.
;; If we don't know which symbol we're assigning to, we do not know
;; the value of any variable in scope."
;;   ;; We don't know the value of x after `set', even though we knew it
;;   ;; before.
;;   (should-partially-simplify
;;    '(progn (set foo 1) x)
;;    '((x . 1))
;;    '(progn (set foo 1) x))
;;   ;; If we do know which symbol we're assigning, proceed as usual.
;;   (should-fully-simplify
;;    '(progn (set sym 1) x)
;;    '((sym . 'x))
;;    1))

(ert-deftest peval--let ()
  ;; Simplify body.
  (should-partially-simplify
   '(let (a) y x)
   '((x . 1))
   '(progn y 1))
  ;; Simplify variable values
  (should-partially-simplify
   '(let ((a (+ c (1+ 1))) (b (foo))))
   nil
   '(let ((a (+ c 2)) (b (foo)))))
  ;; Empty body.
  (should-partially-simplify
   '(let ((x (foo))))
   nil
   '(let ((x (foo))))))

(ert-deftest peval--let* ()
  ;; Simplify body.
  (should-fully-simplify
   '(let* ((x 1) (y (1+ x))) y)
   nil
   2))

(ert-deftest peval--let-new-binding ()
  ;; Simplify body.
  (should-fully-simplify
   '(let ((a 1)) (1+ a))
   nil
   2)
  ;; Bindings should not leak out of the let statement.
  (should-partially-simplify
   '(progn (let ((a 2)) (+ a b)) a)
   nil
   '(progn (+ 2 b) a)))

(ert-deftest peval--or ()
  ;; Remove nil values.
  (should-partially-simplify
   '(or nil x y z)
   '((x . nil))
   '(or y z))
  ;; Simplify a single value.
  (should-partially-simplify
   '(or x y)
   '((x . nil))
   'y)
  ;; Stop on first truthy value.
  (should-fully-simplify
   '(or x y)
   '((x . "foo"))
   "foo")
  ;; Stop on a later truthy value.
  (should-partially-simplify
   '(or x t y)
   nil
   '(or x t))
  ;; All falsy values
  (should-fully-simplify
   '(or x y)
   '((x . nil) (y . nil))
   nil))

(ert-deftest peval--bool ()
  (should-fully-simplify
   'nil
   nil
   nil)
  (should-fully-simplify
   't
   nil
   t))

(ert-deftest peval--number ()
  (should-fully-simplify
   123
   nil
   123))

(ert-deftest peval--keyword ()
  (should-fully-simplify
   :foo
   nil
   :foo))

(ert-deftest peval--string ()
  (should-fully-simplify
   "foo"
   nil
   "foo"))

(ert-deftest peval--symbol ()
  (should-partially-simplify
   'x nil
   'x)
  (should-fully-simplify
   'x
   '((x . 42))
   42))

(ert-deftest peval--quoted-symbol ()
  (should-fully-simplify
   ''x
   nil
   'x))

(ert-deftest peval--if-by-condition ()
  "We should discard then THEN or the ELSE case
if we can evaluate the condition."
  (should-partially-simplify
   '(if x y z)
   nil
   '(if x y z))
  (should-partially-simplify
   '(if x y z)
   '((x . 42))
   'y)
  (should-partially-simplify
   '(if x y z1 z2)
   '((x . nil))
   '(progn z1 z2)))

(ert-deftest peval--if-body ()
  "We should always simplify the THEN and ELSE."
  (should-partially-simplify
   '(if x y z)
   '((y . 42) (z . 41))
   '(if x 42 41))
  ;; ELSE can be multiple forms.
  (should-partially-simplify
   '(if x y foo1 foo2)
   '((foo2 . 123))
   '(if x y foo1 123)))

(ert-deftest peval--if-condition ()
  "We should always simplify the COND."
  (should-partially-simplify
   '(if (if t x a) y z)
   '((y . 42) (z . 41))
   '(if x 42 41)))

(ert-deftest peval--if-without-else ()
  (should-partially-simplify
   '(if t y)
   nil
   'y)
  (should-fully-simplify
   '(if nil y)
   nil
   nil))

(ert-deftest peval--zip-bindings ()
  ;; Basic case
  (should
   (equal
    (peval--zip-bindings
     '(1 2 3)
     '(x y z))
    (list '(x . 1) '(y . 2) '(z . 3))))
  ;; Skip placeholders.
  (should
   (equal
    (peval--zip-bindings
     `(1 ,peval-placeholder 3)
     '(x y z))
    (list '(x . 1) '(z . 3))))
  ;; Optional
  (should
   (equal
    (peval--zip-bindings
     '(1 2 3)
     '(a b &optional c d))
    (list '(a . 1) '(b . 2) '(c . 3) '(d . nil))))
  ;; Rest
  ;; (should
  ;;  (equal
  ;;   (peval--zip-bindings
  ;;    '(1 2 3)
  ;;    '(a b &rest c))
  ;;   (list '(a 1) '(b 2) '(c (3)))))
  )

(ert-deftest peval-smoke-test ()
  "Ensure we can call the interactive function."
  (peval))
