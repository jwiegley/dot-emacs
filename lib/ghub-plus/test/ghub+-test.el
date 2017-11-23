(require 'ghub+)

(ert-deftest basic ()
  (should
   (let* ((repo '((owner (login . "vermiculus"))
                  (name . "ghub-plus")))
          (repo  (ghubp-get-repos-owner-repo repo)))
     (= 82884749 (alist-get 'id repo)))))

(ert-deftest ghubp-test-ratelimit-utils ()
  (let ((ghub-response-headers
         '(("X-RateLimit-Limit" . "5000")
           ("X-RateLimit-Remaining" . "4774")
           ("X-RateLimit-Reset" . "1501809984"))))
    (let-alist (ghubp-ratelimit)
      (should (equal .remaining 4774))
      (should (equal .reset '(22915 52544))))))

(ert-deftest lint-unused-args ()
  (should (lint "ghub+.el" #'lint-unused-args 'per-form)))

(ert-deftest lint-undeclared-args ()
  (should (lint "ghub+.el" #'lint-undeclared-standard-args)))

(ert-deftest lint-ext-reference-in-name ()
  (should (lint "ghub+.el" #'lint-ext-reference-in-name 'per-form)))

(ert-deftest linter-selftest ()
  (message ">>> Start linter self-tests")

  (should (lint-unused-args '(defapiget-ghubp "/rate_limit" "" "" (repo issue) "/:repo.thing")))
  (should (lint-unused-args '(defapiget-ghubp "/rate_limit" "" "" (repo) "/:repo.thing/:issue.thing")))
  (should (lint-ext-reference-in-name '(defapiget-ghubp "/rate.limit" "" "" (repo) "/:repo.thing/:issue.thing")))
  (should-not (lint-unused-args '(defapiget-ghubp "/some_call_with_no_args" "some-desc" "some-url"
                                   :post-process (lambda (o) (ghubp--post-process o '(subject))))))
  (should-not (lint-unused-args '(defapiget-ghubp "/some_call_with_no_args" "some-desc" "some-url")))

  (should (lint-standard-args-undeclared--internal
           '(defapiget-ghubp "/some_call_with_new_args" "some-doc" "some-link" (repo issue weird) "")
           '(repo issue)))
  (should-not (lint-standard-args-undeclared--internal
               '(defapiget-ghubp "/some_call_with_new_args" "some-doc" "some-link" (repo issue) "")
               '(repo issue)))
  (should-not (lint-standard-args-undeclared--internal
               '(defapiget-ghubp "/some_call_with_new_args" "some-doc" "some-link" (repo) "")
               '(repo issue)))
  (should-not (lint-standard-args-undeclared--internal
               '(defapiget-ghubp "/some_call_with_new_args" "some-doc" "some-link" "")
               '(repo issue)))
  (should-not (lint-standard-args-undeclared--internal
               '(defapiget-ghubp "/some_call_with_new_args" "some-doc" "some-link")
               '(repo issue)))

  (message "<<< End linter self-tests"))
