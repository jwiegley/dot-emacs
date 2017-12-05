(require 'ert)
(require 'refine)

(defvar refine--test-var)

(ert-deftest refine-insert ()
  (setq refine--test-var (list 1 2 3))
  (let ((original refine--test-var))
    (refine--insert 'refine--test-var 1 "foo")
    ;; We should have inserted the value.
    (should (equal refine--test-var (list 1 "foo" 2 3)))
    ;; We should have mutated in place, so we still have the same cons
    ;; cell.
    (should (eq refine--test-var original))
    ;; The tails should also be the same cons cell.
    (should (eq (last refine--test-var) (last original)))))

(ert-deftest refine-list-insert-at-end ()
  "Test we handle the append case correctly."
  (setq refine--test-var (list 1 2 3))
  (let ((original refine--test-var))
    (refine--insert 'refine--test-var 3 "foo")
    (should (equal refine--test-var (list 1 2 3 "foo")))))

(ert-deftest refine-pop ()
  (setq refine--test-var (list 1 2 3))
  (let ((original refine--test-var))
    (refine--pop 'refine--test-var 1)
    ;; We should have popped the value
    (should (equal refine--test-var (list 1 3)))
    ;; We should have mutated in place, so we still have the same cons
    ;; cell.
    (should (eq refine--test-var original))
    ;; The tails should also be the same cons cell.
    (should (eq (last refine--test-var) (last original)))))

(ert-deftest refine-move-element ()
  (let ((my-list '(a b c d e)))
    ;; Move 'b two positions forward.
    (refine--move-element my-list 1 2)
    (should
     (equal my-list '(a c d b e)))))
