;;; org-ql-semantic-test.el --- Tests for org-ql-semantic  -*- lexical-binding: t; -*-

;;; Commentary:

;; Tests for the distance filtering applied to `org db search' results.

;;; Code:

(require 'ert)
(require 'org-ql-semantic)

(defun org-ql-semantic-test--results (&rest distances)
  "Return search results carrying DISTANCES, in the order given."
  (mapcar (lambda (d) (list (cons 'distance d))) distances))

(defun org-ql-semantic-test--distances (results)
  "Return the distances of RESULTS."
  (mapcar (lambda (r) (alist-get 'distance r)) results))

(ert-deftest org-ql-semantic-test-filter-keeps-hits-near-the-best ()
  "The distances are those of the query \"Jev decision support\".
Its best hit, at 0.389, holds the query verbatim in its title."
  (let ((org-ql-semantic-max-distance 0.45)
        (org-ql-semantic-relative-distance 0.07))
    (should (equal (org-ql-semantic-test--distances
                    (org-ql-semantic--filter-by-distance
                     (org-ql-semantic-test--results 0.389 0.442 0.458 0.469)))
                   '(0.389 0.442)))))

(ert-deftest org-ql-semantic-test-filter-relative-margin-follows-best ()
  (let ((org-ql-semantic-max-distance 0.5)
        (org-ql-semantic-relative-distance 0.05))
    (should (equal (org-ql-semantic-test--distances
                    (org-ql-semantic--filter-by-distance
                     (org-ql-semantic-test--results 0.20 0.24 0.26 0.40)))
                   '(0.20 0.24)))))

(ert-deftest org-ql-semantic-test-filter-best-need-not-come-first ()
  (let ((org-ql-semantic-max-distance nil)
        (org-ql-semantic-relative-distance 0.05))
    (should (equal (org-ql-semantic-test--distances
                    (org-ql-semantic--filter-by-distance
                     (org-ql-semantic-test--results 0.40 0.20 0.24)))
                   '(0.20 0.24)))))

(ert-deftest org-ql-semantic-test-filter-absolute-ceiling-still-applies ()
  (let ((org-ql-semantic-max-distance 0.45)
        (org-ql-semantic-relative-distance 0.07))
    (should-not (org-ql-semantic--filter-by-distance
                 (org-ql-semantic-test--results 0.47 0.48)))))

(ert-deftest org-ql-semantic-test-filter-each-limit-can-be-disabled ()
  (let ((results (org-ql-semantic-test--results 0.30 0.40 0.60)))
    (let ((org-ql-semantic-max-distance 0.5)
          (org-ql-semantic-relative-distance nil))
      (should (equal (org-ql-semantic-test--distances
                      (org-ql-semantic--filter-by-distance results))
                     '(0.30 0.40))))
    (let ((org-ql-semantic-max-distance nil)
          (org-ql-semantic-relative-distance nil))
      (should (equal (org-ql-semantic--filter-by-distance results) results)))))

(ert-deftest org-ql-semantic-test-filter-missing-distance-is-unrelated ()
  (let ((org-ql-semantic-max-distance 0.5)
        (org-ql-semantic-relative-distance 0.07))
    (should (equal (org-ql-semantic-test--distances
                    (org-ql-semantic--filter-by-distance
                     (list '((distance . 0.30)) '((title . "no distance")))))
                   '(0.30)))))

(provide 'org-ql-semantic-test)
;;; org-ql-semantic-test.el ends here
