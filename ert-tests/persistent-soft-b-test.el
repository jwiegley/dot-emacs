;;;
;;; persistent-soft.el tests -- disk persistence
;;;
;;; Test whether values saved during persistent-soft-a-test.el can
;;; be read by a new Emacs invocation.
;;;
;;; Directory "test_output" should already exist and be populated
;;; when this test is run.
;;;


;;; requires and setup

(when load-file-name
  (setq pcache-directory (expand-file-name "test_output/" (file-name-directory load-file-name)))
  (setq package-enable-at-startup nil)
  (setq package-load-list '((pcache t)
                            (list-utils t)))
  (when (fboundp 'package-initialize)
    (package-initialize)))

(require 'list-utils)
(require 'persistent-soft)

;;; features

(ert-deftest persistent-soft-b:a-feature-01 nil
  (should (featurep 'pcache)))


;;; files and locations

(ert-deftest persistent-soft-b:b-files-01 nil
  (should
   (file-exists-p pcache-directory)))

(ert-deftest persistent-soft-b:b-files-02 nil
  (should
   (persistent-soft-location-readable "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-b:b-files-03 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (should-not
   (persistent-soft-location-readable "ert-test-persistent-soft-location-2")))


;;; data types

(ert-deftest persistent-soft-b:c-data-types-01 nil
  (let ((value "string"))
    (should
     (persistent-soft-exists-p 'string-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'string-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-02 nil
  (let ((value "string with properties"))
    (callf propertize value :face 'bold)
    (should
     (persistent-soft-exists-p 'string-with-properties-key "ert-test-persistent-soft-location-1"))
    (should (equal-including-properties value
                   (persistent-soft-fetch 'string-with-properties-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-03 nil
  (let ((value '(1 2 "3")))
    (should
     (persistent-soft-exists-p 'list-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'list-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-04 nil
  (let ((value '[1 2 "3"]))
    (should
     (persistent-soft-exists-p 'vector-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'vector-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-05 nil
  (should
   (persistent-soft-exists-p 'hash-key "ert-test-persistent-soft-location-1"))
  (let ((hash (persistent-soft-fetch 'hash-key "ert-test-persistent-soft-location-1")))
    (should (hash-table-p hash))
    (dolist (num (number-sequence 1 1000))
      (should (equal (number-to-string num)
                     (gethash num hash))))))

(ert-deftest persistent-soft-b:c-data-types-06 nil
  (let ((value '(1 2 ("3" (4 nil) 7 (8 (8 (8 8))) '[9 9 9]))))
    (should
     (persistent-soft-exists-p 'list-of-lists-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'list-of-lists-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-07 nil
  "Todo: correctly reconstitute cyclic lists"
  :expected-result :failed
  (let ((value '(a b c d e f g h)))
    (nconc value value)
    (should
     (persistent-soft-exists-p 'cyclic-list-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'cyclic-list-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-08 nil
  (let ((value '[1 2 [3 4 5] [6 [7 [8 9]]]]))
    (should
     (persistent-soft-exists-p 'vector-of-vectors-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'vector-of-vectors-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-09 nil
  (let ((value 3))
    (should
     (persistent-soft-exists-p 'integer-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'integer-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-10 nil
  (let ((value 3.14))
    (should
     (persistent-soft-exists-p 'float-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'float-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-11 nil
  (let ((value 'symbol))
    (should
     (persistent-soft-exists-p 'symbol-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'symbol-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-12 nil
  (let ((value (with-temp-buffer
                 (emacs-lisp-mode)
                 (syntax-table))))
    (should
     (persistent-soft-exists-p 'char-table-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'char-table-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-13 nil
  (let ((value (make-bool-vector 10 nil)))
    (should
     (persistent-soft-exists-p 'bool-vector-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'bool-vector-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-14 nil
  (let ((value #'(lambda () t)))
    (should
     (persistent-soft-exists-p 'lambda-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'lambda-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-15 nil
  (let ((value (make-byte-code '(args) nil nil 0)))
    (should
     (persistent-soft-exists-p 'byte-code-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'byte-code-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-16 nil
  (let ((value (make-tconc)))
    (tconc-list value '(1 2 3))
    (tconc-list value '(4 5))
    (should
     (persistent-soft-exists-p 'defstruct-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'defstruct-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-17 nil
  (let ((value (make-sparse-keymap)))
    (define-key value (kbd "a") 'ignore)
    (should
     (persistent-soft-exists-p 'keymap-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'keymap-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:c-data-types-18 nil
  (let ((value '[object tester-class "my_id" unbound]))
    (should
     (persistent-soft-exists-p 'object-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'object-key "ert-test-persistent-soft-location-1")))))


;;; large values

(ert-deftest persistent-soft-b:d-large-values-01 nil
  "Long list without sanity check"
  (let ((value (mapcar 'number-to-string (number-sequence 100000 200000))))
    (should
     (persistent-soft-exists-p 'long-list-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'long-list-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:d-large-values-02 nil
  "Long list with sanity check"
  (let ((value (mapcar 'number-to-string (number-sequence 100000 200000))))
    (should
     (persistent-soft-exists-p 'long-list-sanitized-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'long-list-sanitized-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:d-large-values-03 nil
  "Deep list without sanity check"
  (let ((value (mapcar 'number-to-string (number-sequence 1 10))))
    (dotimes (i 10)
      (push value value))
    (should
     (persistent-soft-exists-p 'deep-list-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'deep-list-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-b:d-large-values-04 nil
  "Deep list with sanity check"
  (let ((value (mapcar 'number-to-string (number-sequence 1 10))))
    (dotimes (i 10)
      (push value value))
    (should
     (persistent-soft-exists-p 'deep-list-sanitized-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'deep-list-sanitized-key "ert-test-persistent-soft-location-1")))))


;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions)
;; End:
;;

;;; persistent-soft-b-test.el ends here
