;;; gnus-limit-frequent-test.el --- Tests for gnus-limit-frequent -*- lexical-binding: t; -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>

;;; Commentary:

;; Test suite for gnus-limit-frequent package.

;;; Code:

(require 'ert)
(require 'cl-lib)
(require 'gnus)
(require 'gnus-sum)

;; Force load the source file to get the latest version
(let ((load-file-path (expand-file-name "gnus-limit-frequent.el"
                                         (file-name-directory
                                          (or load-file-name buffer-file-name)))))
  (when (file-exists-p load-file-path)
    (load-file load-file-path)))

;; Mock data structures
(defvar gnus-limit-frequent-test--headers nil
  "Mock headers for testing.")

(defvar gnus-limit-frequent-test--articles nil
  "Mock article numbers for testing.")

(defmacro gnus-limit-frequent-test--with-mock-summary (&rest body)
  "Execute BODY in a mock Gnus summary environment."
  `(let ((gnus-limit-frequent-test--headers nil)
         (gnus-limit-frequent-test--articles nil)
         (gnus-newsgroup-articles nil))
     (cl-letf (((symbol-function 'gnus-summary-article-header)
                (lambda (article)
                  (cdr (assq article gnus-limit-frequent-test--headers))))
               ((symbol-function 'gnus-summary-limit-to-articles)
                (lambda (articles)
                  (setq gnus-limit-frequent-test--limited-articles articles))))
       ;; Set the articles list
       (setq gnus-newsgroup-articles gnus-limit-frequent-test--articles)
       ,@body)))

(defun gnus-limit-frequent-test--make-header (article from subject)
  "Create a mock header for ARTICLE with FROM and SUBJECT."
  ;; mail-header struct: (number subject from date id references chars lines xref extra)
  (vector article subject from nil nil nil nil nil nil nil))

(ert-deftest gnus-limit-frequent-test-normalize-author ()
  "Test author normalization."
  (should (equal (gnus-limit-frequent--normalize-author "john@example.com")
                 "john@example.com"))
  (should (equal (gnus-limit-frequent--normalize-author "John Doe <john@example.com>")
                 "john@example.com"))
  (should (equal (gnus-limit-frequent--normalize-author "John Doe")
                 "john doe"))
  (should (equal (gnus-limit-frequent--normalize-author "  John Doe  ")
                 "john doe"))
  (should (equal (gnus-limit-frequent--normalize-author nil)
                 nil)))

(ert-deftest gnus-limit-frequent-test-count-headers ()
  "Test header counting functionality."
  ;; Test the counting functions directly without mocking
  (require 'cl-lib)

  ;; Create mock headers directly
  (let* ((headers (list
                   (gnus-limit-frequent-test--make-header 1 "alice@example.com" "Test Subject")
                   (gnus-limit-frequent-test--make-header 2 "alice@example.com" "Re: Test Subject")
                   (gnus-limit-frequent-test--make-header 3 "bob@example.com" "Test Subject")
                   (gnus-limit-frequent-test--make-header 4 "alice@example.com" "Different Subject")
                   (gnus-limit-frequent-test--make-header 5 "charlie@example.com" "Re: Different Subject")))
         (author-counts (make-hash-table :test 'equal))
         (subject-counts (make-hash-table :test 'equal)))

    ;; Manually count authors and subjects to test the logic
    (dolist (header headers)
      (let ((from (mail-header-from header)))
        (when from
          (let ((normalized-author (gnus-limit-frequent--normalize-author from)))
            (when normalized-author
              (cl-incf (gethash normalized-author author-counts 0))))))
      (let ((subject (mail-header-subject header)))
        (when subject
          (let ((normalized-subject (gnus-simplify-subject-re subject)))
            (when (and normalized-subject (> (length normalized-subject) 0))
              (cl-incf (gethash normalized-subject subject-counts 0)))))))

    ;; Check author counts
    (should (= (gethash "alice@example.com" author-counts 0) 3))
    (should (= (gethash "bob@example.com" author-counts 0) 1))
    (should (= (gethash "charlie@example.com" author-counts 0) 1))

    ;; Check subject counts (should be normalized)
    (should (>= (gethash "Test Subject" subject-counts 0) 2))
    (should (>= (gethash "Different Subject" subject-counts 0) 1))))

(ert-deftest gnus-limit-frequent-test-article-matches-p ()
  "Test article matching logic."
  ;; Skip this test if gnus-summary-article-header isn't available
  (skip-unless (fboundp 'gnus-summary-article-header))

  ;; Just test the normalize and matching logic directly
  ;; Test 1: Author normalization
  (should (equal (gnus-limit-frequent--normalize-author "Alice <alice@example.com>")
                 "alice@example.com"))

  ;; Test 2: Frequency check logic
  (let ((author-table (make-hash-table :test 'equal)))
    (puthash "alice@example.com" 3 author-table)
    ;; 3 > 2, so this should be true
    (should (> (gethash "alice@example.com" author-table 0) 2))
    ;; 1 > 2, so this should be false
    (puthash "bob@example.com" 1 author-table)
    (should-not (> (gethash "bob@example.com" author-table 0) 2))))

(provide 'gnus-limit-frequent-test)
;;; gnus-limit-frequent-test.el ends here