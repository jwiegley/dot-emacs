;;;
;;; persistent-soft.el tests -- cleanup
;;;
;;; Directory "test_output" should already exist when this test is run.
;;; Directory "test_output_2" may already exist when this test is run.
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

(ert-deftest persistent-soft-z:a-feature-01 nil
  (should (featurep 'pcache)))


;;; files and locations

(ert-deftest persistent-soft-z:b-files-01 nil
  (should
   (persistent-soft-location-destroy "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-z:b-files-02 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (should
   (persistent-soft-location-destroy "ert-test-persistent-soft-location-2")))

(ert-deftest persistent-soft-z:b-files-03 nil
  (should-not
   (persistent-soft-location-readable "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-z:b-files-04 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (should-not
   (persistent-soft-location-readable "ert-test-persistent-soft-location-2")))

(ert-deftest persistent-soft-z:b-files-05 nil
  (let ((pcache-directory pcache-directory))
    (setq pcache-directory (replace-regexp-in-string "test_output" "test_output_2" pcache-directory))
    (should
     (persistent-soft-location-destroy "ert-test-persistent-soft-location-1"))))

(ert-deftest persistent-soft-z:b-files-06 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (let ((pcache-directory pcache-directory))
    (setq pcache-directory (replace-regexp-in-string "test_output" "test_output_2" pcache-directory))
    (should
     (persistent-soft-location-destroy "ert-test-persistent-soft-location-2"))))

(ert-deftest persistent-soft-z:b-files-07 nil
  (let ((pcache-directory pcache-directory))
    (setq pcache-directory (replace-regexp-in-string "test_output" "test_output_2" pcache-directory))
    (should-not
     (persistent-soft-location-readable "ert-test-persistent-soft-location-1"))))

(ert-deftest persistent-soft-z:b-files-08 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (let ((pcache-directory pcache-directory))
    (setq pcache-directory (replace-regexp-in-string "test_output" "test_output_2" pcache-directory))
    (should-not
     (persistent-soft-location-readable "ert-test-persistent-soft-location-2"))))


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

;;; persistent-soft-a-test.el ends here
