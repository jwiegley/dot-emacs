;;;
;;; persistent-soft.el tests -- soft-failure when library not present.
;;;
;;; Test some boilerplate code for graceful failure when persistent-soft.el
;;; itself is not available.
;;;
;;; Directory "test_output" should already exist and be populated when
;;; this test is run.
;;;


;;; requires and setup

(when load-file-name
  (setq pcache-directory (expand-file-name "test_output/" (file-name-directory load-file-name))))

(setq features (remq 'persistent-soft features))
(fmakunbound 'persistent-soft-exists-p)
(fmakunbound 'persistent-soft-fetch)
(fmakunbound 'persistent-soft-flush)
(fmakunbound 'persistent-soft-store)

(defun persistent-softest-store (symbol value location &optional expiration)
  "Call `persistent-soft-store' but don't fail when library not present."
  (ignore-errors (persistent-soft-store symbol value location expiration)))
(defun persistent-softest-fetch (symbol location)
  "Call `persistent-soft-fetch' but don't fail when library not present."
  (ignore-errors (persistent-soft-fetch symbol location)))
(defun persistent-softest-exists-p (symbol location)
  "Call `persistent-soft-exists-p' but don't fail when library not present."
  (ignore-errors (persistent-soft-exists-p symbol location)))
(defun persistent-softest-flush (location)
  "Call `persistent-soft-flush' but don't fail when library not present."
  (ignore-errors (persistent-soft-flush location)))
(defun persistent-softest-location-readable (location)
  "Call `persistent-soft-location-readable' but don't fail when library not present."
  (ignore-errors (persistent-soft-location-readable location)))
(defun persistent-softest-location-destroy (location)
  "Call `persistent-soft-location-destroy' but don't fail when library not present."
  (ignore-errors (persistent-soft-location-destroy location)))


;;; features

(ert-deftest persistent-soft-e:a-feature-01 nil
  (should-not (featurep 'persistent-soft)))


;;; files and locations

(ert-deftest persistent-soft-e:b-files-01 nil
  (should
   (file-exists-p pcache-directory)))

(ert-deftest persistent-soft-e:b-files-02 nil
  (should-not
   (persistent-softest-location-readable "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:b-files-03 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (should-not
   (persistent-softest-location-readable "ert-test-persistent-soft-location-2")))

(ert-deftest persistent-soft-e:b-files-04 nil
  (should-not
   (persistent-softest-location-destroy "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:b-files-05 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (should-not
   (persistent-softest-location-destroy "ert-test-persistent-soft-location-2")))


;;; data types

(ert-deftest persistent-soft-e:c-data-types-01 nil
  (should-not
   (persistent-softest-exists-p 'string-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'string-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-02 nil
  (should-not
   (persistent-softest-exists-p 'string-with-properties-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'string-with-properties-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-03 nil
  (should-not
   (persistent-softest-exists-p 'list-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'list-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-04 nil
  (should-not
   (persistent-softest-exists-p 'vector-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'vector-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-05 nil
  (should-not
   (persistent-softest-exists-p 'hash-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'hash-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-06 nil
  (should-not
   (persistent-softest-exists-p 'list-of-lists-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'list-of-lists-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-07 nil
  (should-not
   (persistent-softest-exists-p 'cyclic-list-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'cyclic-list-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-08 nil
  (should-not
   (persistent-softest-exists-p 'vector-of-vectors-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'vector-of-vectors-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-09 nil
  (should-not
   (persistent-softest-exists-p 'integer-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'integer-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-10 nil
  (should-not
   (persistent-softest-exists-p 'float-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'float-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-11 nil
  (should-not
   (persistent-softest-exists-p 'symbol-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'symbol-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-12 nil
  (should-not
   (persistent-softest-exists-p 'char-table-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'char-table-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-13 nil
  (should-not
   (persistent-softest-exists-p 'bool-vector-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'bool-vector-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-14 nil
  (should-not
   (persistent-softest-exists-p 'lambda-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'lambda-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-15 nil
  (should-not
   (persistent-softest-exists-p 'byte-code-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'byte-code-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-16 nil
  (should-not
   (persistent-softest-exists-p 'defstruct-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'defstruct-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-17 nil
  (should-not
   (persistent-softest-exists-p 'keymap-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'keymap-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:c-data-types-18 nil
  (should-not
   (persistent-softest-exists-p 'object-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'object-key "ert-test-persistent-soft-location-1")))


;;; large values

(ert-deftest persistent-soft-e:d-large-values-01 nil
  "Long list without sanity check"
  (should-not
   (persistent-softest-exists-p 'long-list-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'long-list-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:d-large-values-02 nil
  "Long list with sanity check"
  (should-not
   (persistent-softest-exists-p 'long-list-sanitized-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'long-list-sanitized-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:d-large-values-03 nil
  "Deep list without sanity check"
  (should-not
   (persistent-softest-exists-p 'deep-list-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'deep-list-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-e:d-large-values-04 nil
  "Deep list with sanity check"
  (should-not
   (persistent-softest-exists-p 'deep-list-sanitized-key "ert-test-persistent-soft-location-1"))
  (should-not
   (persistent-softest-fetch 'deep-list-sanitized-key "ert-test-persistent-soft-location-1")))


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

;;; persistent-soft-e-test.el ends here
