;;; TODO:

;; * more test

;;; Code:

(require 'ert)

;;
;; unit test
;;

(ert-deftest erefactor-local-bindings ()
  :tags '(erefactor)

  (should (erefactor--local-binding-p 'v '(defun f (v))))
  (should (erefactor--local-binding-p 'v '(lambda (v))))
  (should (erefactor--local-binding-p 'v '(let ((v v1)))))
  (should (erefactor--local-binding-p 'tag '(catch 'tag)))

  (should-not (erefactor--local-binding-p 'v '(defun f (v1) v)))
  (should-not (erefactor--local-binding-p 'v '(lambda (v1) v)))
  (should-not (erefactor--local-binding-p 'v '(let ((v1 val)) v)))
  (should-not (erefactor--local-binding-p 'tag '(catch 'tag1 tag))))

;; TODO comment out for now
(ert-deftest erefactor-local-bindings-in-macro ()
  :tags '(erefactor)

  ;; need to macro expand when execute time
  (require 'cl)

  (should (erefactor--macroexpand-contains-p 'v '(defun* f (v))))
  (should (erefactor--macroexpand-contains-p 'k1 '(defun* f (v1 &key k1))))
  (should-not (erefactor--macroexpand-contains-p 'v '(defun* f (v1) v)))

  ;; check ignoring failed (defface) form expansion
  (should-not (erefactor--macroexpand-contains-p 'v1 '(when test (case v1 (defface)))))

  ;; cannot test `erefactor--local-fbinding' because that move point.
  )



;; (macroexpand-all '(erefactor--macroexpand-contains-p 'v '(defun* f (v))))

