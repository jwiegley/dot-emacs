;;; magithub-tests.el --- tests for Magithub

;; Copyright (C) 2016  Sean Allred
;;
;; License: GPLv3

;;; Code:

(require 'ert)
(require 'magithub-core)
(require 'ghub+)

(setq ghubp-request-override-function
      #'magithub-mock-ghub-request)

(defmacro magithub-test-cache-with-new-cache (plist &rest body)
  (declare (indent 1))
  `(let ((magithub-cache-class-refresh-seconds-alist ',plist)
         (magithub-cache--cache (make-hash-table)))
     ,@body))

(ert-deftest magithub-test-cache ()
  (magithub-test-cache-with-new-cache ((:test . 30))
    (should (equal t (magithub-cache :test t)))))

(ert-deftest magithub-test-origin-parse ()
  "Tests issue #105."
  (let ((repo '((owner (login . "vermiculus"))
                (name . "magithub"))))
    (should (equal repo (magithub--url->repo "git@github.com:vermiculus/magithub.git")))
    (should (equal repo (magithub--url->repo "git@github.com:vermiculus/magithub")))
    (should (equal repo (magithub--url->repo "git+ssh://github.com/vermiculus/magithub")))
    (should (equal repo (magithub--url->repo "ssh://git@github.com/vermiculus/magithub")))))

(ert-deftest magithub-test-source-repo ()
  "Test basic API functionality.
This tests everything from checking API availability to
determining that we're in a GitHub repository to actually making
cached API calls."
  (let ((magithub--api-last-checked (current-time)))
    (should (magithub-source--sparse-repo))
    (should (magithub-repo))
    (should (let ((magithub-cache t))     ; force API call
              (magithub-repo)))
    (should (let ((magithub-cache nil))   ; force cache read
              (magithub-repo)))))

;;; magithub-test.el ends here
