;;;
;;; persistent-soft.el tests -- pcache.el soft-failure
;;;
;;; Test for graceful failure when pcache.el is not available.
;;;
;;; Directory "test_output" should already exist and be populated when
;;; this test is run.
;;;


;;; requires and setup

(when load-file-name
  (setq pcache-directory (expand-file-name "test_output/" (file-name-directory load-file-name))))

(require 'persistent-soft)
(setq features (remq 'pcache features))
(fmakunbound 'pcache-get)
(fmakunbound 'pcache-has)
(fmakunbound 'pcache-put)
(fmakunbound 'pcache-repository)
(fmakunbound 'pcache-save)


;;; features

(ert-deftest persistent-soft-d:a-feature-01 nil
  (should-not (featurep 'pcache)))


;;; files and locations

(ert-deftest persistent-soft-d:b-files-01 nil
  (should
   (file-exists-p pcache-directory)))

(ert-deftest persistent-soft-d:b-files-02 nil
  (should-not
   (persistent-soft-location-readable "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:b-files-03 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (should-not
   (persistent-soft-location-readable "ert-test-persistent-soft-location-2")))


;;; data types

(ert-deftest persistent-soft-d:c-data-types-01 nil
  (should-not
   (persistent-soft-exists-p 'string-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'string-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-02 nil
  (should-not
   (persistent-soft-exists-p 'string-with-properties-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'string-with-properties-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-03 nil
  (should-not
   (persistent-soft-exists-p 'list-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'list-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-04 nil
  (should-not
   (persistent-soft-exists-p 'vector-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'vector-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-05 nil
  (should-not
   (persistent-soft-exists-p 'hash-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'hash-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-06 nil
  (should-not
   (persistent-soft-exists-p 'list-of-lists-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'list-of-lists-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-07 nil
  (should-not
   (persistent-soft-exists-p 'cyclic-list-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'cyclic-list-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-08 nil
  (should-not
   (persistent-soft-exists-p 'vector-of-vectors-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'vector-of-vectors-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-09 nil
  (should-not
   (persistent-soft-exists-p 'integer-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'integer-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-10 nil
  (should-not
   (persistent-soft-exists-p 'float-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'float-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-11 nil
  (should-not
   (persistent-soft-exists-p 'symbol-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'symbol-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-12 nil
  (should-not
   (persistent-soft-exists-p 'char-table-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'char-table-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-13 nil
  (should-not
   (persistent-soft-exists-p 'bool-vector-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'bool-vector-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-14 nil
  (should-not
   (persistent-soft-exists-p 'lambda-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'lambda-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-15 nil
  (should-not
   (persistent-soft-exists-p 'byte-code-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'byte-code-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-16 nil
  (should-not
   (persistent-soft-exists-p 'defstruct-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'defstruct-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-17 nil
  (should-not
   (persistent-soft-exists-p 'keymap-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'keymap-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:c-data-types-18 nil
  (should-not
   (persistent-soft-exists-p 'object-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'object-key "ert-test-persistent-soft-location-1")))


;;; large values

(ert-deftest persistent-soft-d:d-large-values-01 nil
  "Long list without sanity check"
  (should-not
   (persistent-soft-exists-p 'long-list-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'long-list-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:d-large-values-02 nil
  "Long list with sanity check"
  (should-not
   (persistent-soft-exists-p 'long-list-sanitized-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'long-list-sanitized-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:d-large-values-03 nil
  "Deep list without sanity check"
  (should-not
   (persistent-soft-exists-p 'deep-list-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'deep-list-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-d:d-large-values-04 nil
  "Deep list with sanity check"
  (should-not
   (persistent-soft-exists-p 'deep-list-sanitized-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-soft-fetch 'deep-list-sanitized-key "ert-test-persistent-soft-location-1")))


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

;;; persistent-soft-d-test.el ends here
