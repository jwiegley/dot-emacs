(require 'ert)
(require 'refine)

(ert-deftest refine-smoke-test ()
  "Smoke test to ensure that we can show a complex list."
  (refine 'auto-mode-alist))

(ert-deftest refine-unbound-smoke-test ()
  "Smoke test to ensure that we can handle an unbound variable."
  (refine 'no-such-variable)
  (should (equal (s-trim (buffer-string))
                 "no-such-variable is an unbound symbol.")))

(defvar refine--test-var)

(ert-deftest refine-resets-point ()
  "Calling the refine command should reset the point position.
Otherwise, our tests can interfere with each other!"
  (setq refine--test-var '(a b c))
  (refine 'refine--test-var)
  (let ((start-pos (point)))
    (refine-next 2)
    (refine 'refine--test-var)
    (should (equal start-pos (point)))))

(ert-deftest refine-update-preserves-position ()
  "`refine-update' should not move point, even if the value
description changes."
  ;; First, show a refine buffer on a nil value.
  (setq refine--test-var nil)
  (refine 'refine--test-var)
  ;; Move point to the value.
  (refine-next 1)
  (let ((start-line (line-number-at-pos)))
    ;; Set the variable to a list, and update.
    (setq refine--test-var '(1 2 3 4))
    (refine-update)
    ;; Point should still be on the same line.
    (should (equal start-line (line-number-at-pos)))))

(ert-deftest refine-next-symbol-value ()
  "`refine-update' should not move point, even if the value
description changes."
  (setq refine--test-var 'foo)
  (refine 'refine--test-var)
  ;; Move point to the value.
  ;; Warning: when this is broken, it's often an infinite loop!
  (refine-next 1))

(ert-deftest refine-insert-empty-list ()
  "Smoke test to ensure that we can insert into an empty list."
  ;; Open refine on an empty list.
  (setq refine--test-var nil)
  (refine 'refine--test-var)
  ;; Move to the list itself.
  (refine-next 1)
  (refine-insert 'a)
  ;; Verify that we inserted the value we expected.
  (should (equal refine--test-var
                 (list 'a)))
  ;; We should have point positioned on the newly inserted item.
  (should (looking-at "0 'a")))

(ert-deftest refine-edit-lists ()
  "We should be able to call `refine-edit' on a list."
  (setq refine--test-var '(a b c))
  (refine 'refine--test-var)
  (refine-next 1)
  (refine-edit 'xxx)
  (should (equal refine--test-var '(xxx b c))))

(ert-deftest refine-edit-vectors ()
  "We should be able to call `refine-edit' on a vector."
  (setq refine--test-var (vector 1 2 3))
  (refine 'refine--test-var)
  (refine-next 1)
  (refine-edit 99)
  (should (equal refine--test-var (vector 99 2 3))))

(defcustom refine--test-var-no-choices '(x y)
  "Apparently cask insists on a docstring here."
  :type '(repeat (choice symbol)))

(ert-deftest refine-cycle-but-symbols-without-choices ()
  "We should call user-error if defcustom does not specify
specific possibilities."
  (refine 'refine--test-var-no-choices)
  ;; Move to the first item.
  (refine-next 1)
  (let ((user-error-called nil))
    (condition-case err
        (refine-cycle)
      (user-error (setq user-error-called t)))
    (should user-error-called)))

(defcustom refine--test-var-choices-set '(baz)
  "Apparently cask insists on a docstring here."
  :type '(set
          (const :tag "Foo" foo)
          (const :tag "Bar" bar)
          (const :tag "Baz" baz)))

;; TODO: should we be smarter and prevent users inserting duplicates?
(ert-deftest refine-cycle-choices-set ()
  "If our options are a set, we should still cycle."
  (refine 'refine--test-var-choices-set)
  ;; Move point to the first value.
  (refine-next 1)
  ;; Cycle once, which should wrap around.
  (refine-cycle)
  (should (equal refine--test-var-choices-set '(foo))))

(defcustom refine--test-var-radio 'a
  "Apparently cask insists on a docstring here."
  :type '(radio
          (const :tag "Foo" a)
          (const :tag "Bar" b)
          (const :tag "Baz" c)))

(ert-deftest refine-cycle-choices-set ()
  "If our options are a set, we should still cycle."
  (refine 'refine--test-var-radio)
  ;; Move point to the first value.
  (refine-next 1)
  ;; Cycle once, which should change the value, even though it's not a
  ;; list.
  (refine-cycle)
  (should (equal refine--test-var-radio 'b)))

(defcustom refine--test-var-bool nil
  "Apparently cask insists on a docstring here."
  :type 'boolean)

(ert-deftest refine-cycle-bool ()
  "We should be able to cycle booleans."
  (refine 'refine--test-var-bool)
  (refine-cycle)
  (should (eq refine--test-var-bool t)))

(ert-deftest refine-move-forward ()
  "We should be able to move elements forward in lists."
  (setq refine--test-var '(a b c))
  (refine 'refine--test-var)
  (refine-next 1)
  (refine-move-forward 1)
  (should (equal refine--test-var '(b a c))))

(ert-deftest refine-move-backward ()
  "We should be able to move elements backward in lists."
  (setq refine--test-var '(a b c))
  (refine 'refine--test-var)
  (refine-next 3)
  (refine-move-backward 1)
  (should (equal refine--test-var '(a c b))))

(ert-deftest refine-move-forward-without-list ()
  "Fail gracefully if we don't have any list elements to move."
  (setq refine--test-var-bool nil)
  (refine 'refine--test-var-bool)
  (refine-next 1)
  (let ((user-error-called nil))
    (condition-case err
        (refine-move-forward 1)
      (user-error (setq user-error-called t)))
    (should user-error-called)))

;; TODO: move to a better file.
(ert-deftest refine-variables-not-functions ()
  (let ((vars (refine--variables)))
    (should (-contains-p vars 'kill-ring))
    (should (not (-contains-p vars 'message)))))
