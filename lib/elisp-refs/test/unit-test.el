(require 'ert)
(require 'elisp-refs)

;; For Travis CI is recursing more deeply, meaning we hit recursion
;; limits. I suspect this is due to undercover collecting coverage
;; metrics.
(when (getenv "TRAVIS")
  (message "Updating recursion limits from: max-specpdl-size: %s max-lisp-eval-depth: %s "
           max-specpdl-size
           max-lisp-eval-depth)
  (setq max-specpdl-size 2500)
  (setq max-lisp-eval-depth 1000))

(defmacro with-temp-backed-buffer (contents &rest body)
  "Create a temporary file with CONTENTS, and evaluate BODY
whilst visiting that file."
  (let ((filename-sym (make-symbol "filename"))
        (buf-sym (make-symbol "buf")))
    `(let* ((,filename-sym (make-temp-file "with-temp-buffer-and-file"))
            (,buf-sym (find-file-noselect ,filename-sym)))
       (unwind-protect
           (with-current-buffer ,buf-sym
             (insert ,contents)
             (shut-up (save-buffer))
             ,@body)
         (kill-buffer ,buf-sym)
         (delete-file ,filename-sym)))))

(ert-deftest elisp-refs--format-int ()
  "Ensure we format thousands correctly in numbers."
  (should (equal (elisp-refs--format-int 123) "123"))
  (should (equal (elisp-refs--format-int -123) "-123"))
  (should (equal (elisp-refs--format-int 1234) "1,234"))
  (should (equal (elisp-refs--format-int -1234) "-1,234"))
  (should (equal (elisp-refs--format-int 1234567) "1,234,567")))

(ert-deftest elisp-refs--pluralize ()
  (should (equal (elisp-refs--pluralize 0 "thing") "0 things"))
  (should (equal (elisp-refs--pluralize 1 "thing") "1 thing"))
  (should (equal (elisp-refs--pluralize 2 "thing") "2 things"))
  (should (equal (elisp-refs--pluralize 1001 "thing") "1,001 things")))

(ert-deftest elisp-refs--unindent-split-properties ()
  "Ensure we can still unindent when properties are split
into separate region. Regression test for a very subtle bug."
  (let ((s #("e.\n" 0 2 (elisp-refs-start-pos 0) 2 3 (elisp-refs-start-pos 0))))
    (elisp-refs--unindent-rigidly s)))

(ert-deftest elisp-refs--sexp-positions ()
  "Ensure we calculate positions correctly when we're considering
the whole buffer."
  (with-temp-backed-buffer
   "(while list (setq len 1))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (sexp-positions
           (elisp-refs--sexp-positions elisp-refs-buf (point-min) (point-max))))
     (should
      (equal sexp-positions (list '(1 26)))))))

(ert-deftest elisp-refs--sexp-positions-comments ()
  "Ensure we handle comments correctly when calculating sexp positions."
  (with-temp-backed-buffer
   "(while list
  ;; take the head of LIST
  (setq len 1))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (sexp-positions
           (elisp-refs--sexp-positions elisp-refs-buf (1+ (point-min)) (1- (point-max)))))
     ;; The position of the setq should take into account the comment.
     (should
      (equal (nth 2 sexp-positions) '(42 54))))))

(ert-deftest elisp-refs--find-calls-basic ()
  "Find simple function calls."
  (with-temp-backed-buffer
   "(foo)"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should
      (equal calls (list (list '(foo) 1 6)))))))

(ert-deftest elisp-refs--find-calls-sharp-quote ()
  "Find function references using sharp quotes."
  (with-temp-backed-buffer
   "(bar #'foo)"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should
      (equal calls (list (list '(bar #'foo) 1 12)))))))

(ert-deftest elisp-refs--find-calls-in-lambda ()
  "Find function calls in lambda expressions."
  (with-temp-backed-buffer
   "(lambda (foo) (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should
      (equal calls (list (list '(foo) 15 20)))))))

(ert-deftest elisp-refs--find-calls-in-backquote ()
  "Find function calls in backquotes.
Useful for finding references in macros, but this is primarily a
regression test for bugs where we miscalculated position with
backquote forms."
  (with-temp-backed-buffer
   "(baz `(biz (foo 1)))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should
      (equal calls (list (list '(foo 1) 12 19)))))))

(ert-deftest elisp-refs--find-macros-improper-list ()
  "We shouldn't crash if the source code contains improper lists."
  (with-temp-backed-buffer
   "(destructuring-bind (start . end) region\n  (when foo\n    (bar)))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'when
                                            #'elisp-refs--macro-p)))
     (should
      (equal calls (list (list '(when foo (bar)) 44 64)))))))

(ert-deftest elisp-refs--find-calls-nested ()
  "Find nested function calls."
  (with-temp-backed-buffer
   "(baz (bar (foo)))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should
      (equal calls (list (list '(foo) 11 16)))))))

(ert-deftest elisp-refs--find-calls-funcall ()
  "Find calls that use funcall."
  (with-temp-backed-buffer
   "(funcall 'foo)"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should
      (equal calls (list (list '(funcall 'foo) 1 15)))))))

(ert-deftest elisp-refs--find-calls-apply ()
  "Find calls that use apply."
  (with-temp-backed-buffer
   "(apply 'foo '(1 2))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should
      (equal calls (list (list '(apply 'foo '(1 2)) 1 20)))))))

(ert-deftest elisp-refs--find-calls-params ()
  "Function or macro parameters should not be considered function calls."
  (with-temp-backed-buffer
   "(defun bar (foo)) (defsubst bar (foo)) (defmacro bar (foo)) (cl-defun bar (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should (null calls)))))

(ert-deftest elisp-refs--find-calls-let-without-assignment ()
  "We shouldn't confuse let declarations with function calls."
  (with-temp-backed-buffer
   "(let (foo)) (let* (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should (null calls)))))

(ert-deftest elisp-refs--find-calls-let-with-assignment ()
  "We shouldn't confuse let assignments with function calls."
  (with-temp-backed-buffer
   "(let ((foo nil))) (let* ((foo nil)))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should (null calls)))))

(ert-deftest elisp-refs--find-calls-let-with-assignment-call ()
  "We should find function calls in let assignments."
  ;; TODO: actually check positions, this is error-prone.
  (with-temp-backed-buffer
   "(let ((bar (foo)))) (let* ((bar (foo))))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should
      (equal (length calls) 2)))))

(ert-deftest elisp-refs--find-calls-let-body ()
  "We should find function calls in let body."
  (with-temp-backed-buffer
   "(let (bar) (foo)) (let* (bar) (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--function-p)))
     (should (equal (length calls) 2)))))

(ert-deftest elisp-refs--find-macros-basic ()
  "Find simple function calls."
  (with-temp-backed-buffer
   "(foo)"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--macro-p)))
     (should
      (equal calls (list (list '(foo) 1 6)))))))

(ert-deftest elisp-refs--find-macros-in-lambda ()
  "Find macros calls in lambda expressions."
  (with-temp-backed-buffer
   "(lambda (foo) (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--macro-p)))
     (should
      (equal calls (list (list '(foo) 15 20)))))))

(ert-deftest elisp-refs--find-macros-params ()
  "Find simple function calls."
  (with-temp-backed-buffer
   "(defun bar (foo)) (defsubst bar (foo)) (defmacro bar (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--macro-p)))
     (should (null calls)))))

(ert-deftest elisp-refs--find-macros-let-without-assignment ()
  "We shouldn't confuse let declarations with macro calls."
  (with-temp-backed-buffer
   "(let (foo)) (let* (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--macro-p)))
     (should (null calls)))))

(ert-deftest elisp-refs--find-macros-let-with-assignment ()
  "We shouldn't confuse let assignments with macro calls."
  (with-temp-backed-buffer
   "(let ((foo nil) (foo nil))) (let* ((foo nil) (foo nil)))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--macro-p)))
     (should (null calls)))))

(ert-deftest elisp-refs--find-macros-let-with-assignment-call ()
  "We should find macro calls in let assignments."
  (with-temp-backed-buffer
   "(let ((bar (foo)))) (let* ((bar (foo))))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--macro-p)))
     (should
      (equal (length calls) 2)))))

(ert-deftest elisp-refs--find-calls-let-body ()
  "We should find macro calls in let body."
  (with-temp-backed-buffer
   "(let (bar) (foo)) (let* (bar) (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (calls (elisp-refs--read-and-find elisp-refs-buf 'foo
                                            #'elisp-refs--macro-p)))
     (should (equal (length calls) 2)))))

(ert-deftest elisp-refs--find-symbols ()
  "We should find symbols, not their containing forms."
  (with-temp-backed-buffer
   "(foo foo)"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (matches (elisp-refs--read-and-find-symbol elisp-refs-buf 'foo)))
     (should
      (equal
       matches
       (list '(foo 2 5) '(foo 6 9)))))))

(ert-deftest elisp-refs--find-var-basic ()
  "Test the base case of finding variables"
  (with-temp-backed-buffer
   "foo"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (matches (elisp-refs--read-and-find elisp-refs-buf 'foo
                                              #'elisp-refs--variable-p)))
     (should
      (equal
       matches
       (list '(foo 1 4)))))))

(ert-deftest elisp-refs--find-var-in-lambda ()
  "Find variable references in lambda expressions."
  (with-temp-backed-buffer
   "(lambda (foo) (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (matches (elisp-refs--read-and-find elisp-refs-buf 'foo
                                              #'elisp-refs--variable-p)))
     (should
      (equal matches (list (list 'foo 10 13)))))))

(ert-deftest elisp-refs--find-var-ignores-calls ()
  "Function calls are not variable references."
  (with-temp-backed-buffer
   "(baz (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (matches (elisp-refs--read-and-find elisp-refs-buf 'foo
                                              #'elisp-refs--variable-p)))
     (should (null matches)))))

(ert-deftest elisp-refs--find-var-ignores-defs ()
  "Function definitions and macro definitions are not varible references."
  (with-temp-backed-buffer
   "(defun foo ()) (defmacro foo ())"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (matches (elisp-refs--read-and-find elisp-refs-buf 'foo
                                              #'elisp-refs--variable-p)))
     (should (null matches)))))

(ert-deftest elisp-refs--find-var-let-without-assignments ()
  "We should recognise let variables as variable references."
  (with-temp-backed-buffer
   "(let (foo)) (let* (foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (matches (elisp-refs--read-and-find elisp-refs-buf 'foo
                                              #'elisp-refs--variable-p)))
     (should
      (equal
       matches
       (list '(foo 7 10) '(foo 20 23)))))))

(ert-deftest elisp-refs--find-var-let-with-assignments ()
  "We should recognise let variables as variable references."
  (with-temp-backed-buffer
   "(let ((foo 1))) (let* ((foo 2)))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (matches (elisp-refs--read-and-find elisp-refs-buf 'foo
                                              #'elisp-refs--variable-p)))
     (should
      (equal
       matches
       (list '(foo 8 11) '(foo 25 28)))))))

(ert-deftest elisp-refs--find-var-let-body ()
  "We should recognise let variables as variable references."
  (with-temp-backed-buffer
   "(let ((x (1+ foo))) (+ x foo))"
   (let* ((elisp-refs-buf (elisp-refs--contents-buffer (buffer-file-name)))
          (matches (elisp-refs--read-and-find elisp-refs-buf 'foo
                                              #'elisp-refs--variable-p)))
     (should
      (equal
       (length matches)
       2)))))

(ert-deftest elisp-refs--unindent-rigidly ()
  "Ensure we unindent by the right amount."
  ;; Take the smallest amount of indentation, (2 in this case), and
  ;; unindent by that amount.
  (should
   (equal
    (elisp-refs--unindent-rigidly "   foo\n  bar\n    baz")
    " foo\nbar\n  baz"))
  ;; If one of the lines has no indent, do nothing.
  (should
   (equal
    (elisp-refs--unindent-rigidly "foo\n bar")
    "foo\n bar"))
  ;; We should have set elisp-refs-unindented correctly.
  (should
   (equal
    (get-text-property
     0
     'elisp-refs-unindented
     (elisp-refs--unindent-rigidly "  foo"))
    2))
  ;; We should still have elisp-refs-path properties in the entire string.
  (let ((result (elisp-refs--unindent-rigidly
                 (propertize " foo\n bar" 'elisp-refs-path "/foo"))))
    (cl-loop for i from 0 below (length result) do
             (should
              (get-text-property i 'elisp-refs-path result)))))

(ert-deftest elisp-refs--replace-tabs ()
  "Ensure we replace all tabs in STRING."
  (let ((tab-width 4))
    ;; zero tabs
    (should (equal (elisp-refs--replace-tabs " a ") " a "))
    ;; many tabs
    (should (equal (elisp-refs--replace-tabs "a\t\tb") "a        b"))))

(ert-deftest elisp-refs-function ()
  "Smoke test for `elisp-refs-function'."
  (elisp-refs-function 'format)
  (should
   (equal (buffer-name) "*refs: format*")))

(ert-deftest elisp-refs-macro ()
  "Smoke test for `elisp-refs-macro'."
  (elisp-refs-macro 'when)
  (should
   (equal (buffer-name) "*refs: when*")))

(ert-deftest elisp-refs-variable ()
  "Smoke test for `elisp-refs-variable'."
  (elisp-refs-variable 'case-fold-search)
  (should
   (equal (buffer-name) "*refs: case-fold-search*")))

(ert-deftest elisp-refs-special ()
  "Smoke test for `elisp-refs-special'."
  (elisp-refs-special 'prog2)
  (should
   (equal (buffer-name) "*refs: prog2*")))

(ert-deftest elisp-refs-symbol ()
  "Smoke test for `elisp-refs-symbol'."
  (elisp-refs-symbol 'format-message)
  (should
   (equal (buffer-name) "*refs: format-message*")))

(ert-deftest elisp-refs-function-prefix ()
  "Smoke test for searching with a path prefix."
  (elisp-refs-function 'format-message "/usr/share/emacs")
  (should
   (equal (buffer-name) "*refs: format-message*")))

(ert-deftest elisp-refs-next-match ()
  "Ensure movement commands move between results."
  ;; First, get a results buffer.
  (elisp-refs-function 'lsh)
  ;; After moving to the first result, we should have a property that
  ;; tells us where the result came from.
  (elisp-refs-next-match)
  (should
   (not (null (get-text-property (point) 'elisp-refs-start-pos)))))
