(require 'ert)
(require 'loop)

(ert-deftest loop-test-while ()
  "Test basic `loop-while' usage."
  (let ((x 0)
        (sum 0))
    ;; sum the numbers 0 to 9
    (loop-while (< x 10)
      (setq sum (+ sum x))
      (setq x (1+ x)))
    (should (equal sum 45))))

(ert-deftest loop-test-while-break ()
  "Test `loop-break' inside a `loop-while' block."
  (let ((x 0)
        (sum 0))
    ;; sum the numbers 0 to 5
    (loop-while (< x 10)
      (setq sum (+ sum x))
      (setq x (1+ x))
      (when (= x 6)
        (loop-break)))
    (should (equal sum 15))))

(ert-deftest loop-test-while-continue ()
  "Test `loop-continue' inside a `loop-while' block."
  (let ((x 0)
        (sum 0))
    ;; sum the numbers 1, 3, 4, 5
    (loop-while (< x 5)
      (setq x (1+ x))
      (when (= x 2)
        (loop-continue))
      (setq sum (+ sum x)))
    (should (equal sum 13))))

(ert-deftest loop-test-do-while ()
  "Test basic `loop-do-while' usage."
  (let ((x 0)
        (sum 0))
    ;; our condition is false on the first iteration
    (loop-do-while (and (> x 0) (< x 10))
      (setq sum (+ sum x))
      (setq x (1+ x)))
    (should (equal sum 45))))

(ert-deftest loop-test-do-while-continue ()
  "Test `loop-continue' inside a `loop-do-while' block."
  (let ((x 0)
        (sum 0))
    ;; sum the numbers 1, 3, 4, 5
    (loop-while (< x 5)
      (setq x (1+ x))
      (when (= x 2)
        (loop-continue))
      (setq sum (+ sum x)))
    (should (equal sum 13))))

(ert-deftest loop-test-until ()
  "Test basic `loop-until' usage."
  (let ((x 0)
        (sum 0))
    ;; sum the numbers 0 to 9
    (loop-until (= x 10)
      (setq sum (+ sum x))
      (setq x (1+ x)))
    (should (equal sum 45))))

(ert-deftest loop-test-until-break ()
  "Test `loop-break' inside a `loop-until' block."
  (let ((x 0)
        (sum 0))
    ;; sum the numbers 0 to 5
    (loop-until (= x 10)
      (setq sum (+ sum x))
      (setq x (1+ x))
      (when (= x 6)
        (loop-break)))
    (should (equal sum 15))))

(ert-deftest loop-test-until-continue ()
  "Test `loop-continue' inside a `loop-until' block."
  (let ((x 0)
        (sum 0))
    ;; sum the numbers 1, 3, 4, 5
    (loop-until (= x 5)
      (setq x (1+ x))
      (when (= x 2)
        (loop-continue))
      (setq sum (+ sum x)))
    (should (equal sum 13))))

(ert-deftest loop-test-for-each ()
  "Test basic `loop-for-each' usage."
  (let ((sum 0))
    (loop-for-each x (list 1 2 3 4 5 6 7 8 9)
      (setq sum (+ sum x)))
    (should (equal sum 45))))

(ert-deftest loop-test-for-each-break ()
  "Test `loop-break' inside a `loop-for-each' block."
  (let ((sum 0))
    ;; sum the numbers 1 to 5
    (loop-for-each x (list 1 2 3 4 5 6 7 8 9)
      (setq sum (+ sum x))
      (when (= x 5)
        (loop-break)))
    (should (equal sum 15))))

(ert-deftest loop-test-for-each-continue ()
  "Test `loop-continue' inside a `loop-for-each' block."
  (let ((sum 0))
    ;; sum the numbers 1, 3, 4, 5
    (loop-for-each x (list 1 2 3 4 5)
      (when (= x 2)
        (loop-continue))
      (setq sum (+ sum x)))
    (should (equal sum 13))))

(ert-deftest loop-test-for-each-return ()
  "`loop-return' should let us return values from a loop."
  (should
   (equal
    3
    (loop-for-each x (list 1 2 3 4)
      (when (equal x 3)
        (loop-return x))))))

(ert-deftest loop-test-for-each-line ()
  (with-temp-buffer
    (insert "foo\nbar\nbaz")
    (let ((lines nil))
      (loop-for-each-line
        (let ((line-start (progn (beginning-of-line) (point)))
              (line-end (progn (end-of-line) (point))))
          (push (buffer-substring line-start line-end) lines)))
      (should (equal (nreverse lines) '("foo" "bar" "baz"))))))

(ert-deftest loop-test-for-each-line-ignores-movement ()
  "We should execute BODY once for each line, even if point moves around."
  (with-temp-buffer
    (insert "foo\nbar\nbaz")
    (let ((lines nil))
      (loop-for-each-line
        (let ((line-start (progn (beginning-of-line) (point)))
              (line-end (progn (end-of-line) (point))))
          (push (buffer-substring line-start line-end) lines)
          ;; This line should have no effect.
          (forward-line 1)))
      (should (equal (nreverse lines) '("foo" "bar" "baz"))))))

(ert-deftest loop-test-for-each-line-it-line ()
  "We should have `it' set inside `loop-for-each-line'."
  (with-temp-buffer
    (insert "foo\nbar\nbaz")
    (let ((lines nil))
      (loop-for-each-line
        (push it lines))
      (should (equal (nreverse lines) '("foo" "bar" "baz"))))))

(ert-deftest loop-test-for-each-line-break ()
  "Test breaking out of `loop-for-each-line'."
  (with-temp-buffer
    (insert "foo\nbar\nbaz")
    (let ((lines nil))
      (loop-for-each-line
        (let ((line-start (save-excursion (beginning-of-line) (point)))
              (line-end (save-excursion (end-of-line) (point))))
          (when (looking-at "bar")
            (loop-break))
          (push (buffer-substring line-start line-end) lines)))
      (should (equal (nreverse lines) '("foo"))))))

(ert-deftest loop-test-for-each-line-continue ()
  "Test continuing in `loop-for-each-line'."
  (with-temp-buffer
    (insert "foo\nbar\nbaz")
    (let ((lines nil))
      (loop-for-each-line
        (let ((line-start (save-excursion (beginning-of-line) (point)))
              (line-end (save-excursion (end-of-line) (point))))
          (when (looking-at "bar")
            (loop-continue))
          (push (buffer-substring line-start line-end) lines)))
      (should (equal (nreverse lines) '("foo" "baz"))))))

(defun loop-run-tests ()
  "Run all unit tests for loop.el"
  (interactive)
  (ert-run-tests-interactively "loop-test-"))
