;; This file contains your project specific step definitions. All
;; files in this directory whose names end with "-steps.el" will be
;; loaded automatically by Ecukes.

(When "^I execute company-restclient prefix command at current point$"
      (lambda ()
        (setq company-restclient-test-prefix-output
              (company-restclient 'prefix))))

(When "^I execute company-restclient post-completion with \"\\(.*\\)\""
      (lambda (str)
        (company-restclient 'post-completion str)))

(Then "^company-restclient prefix is\\(?: \"\\(.*\\)\"\\|:\\)$"
      (lambda (expected)
        (should (equal company-restclient-test-prefix-output expected))))

(Then "^company-restclient prefix none$"
      (lambda ()
        (should (not company-restclient-test-prefix-output))))

(When "^I execute company-restclient candidates command at current point$"
      (lambda ()
        (let* ((tmp (or (company-restclient 'prefix) 'stop))
               (prefix (if (consp tmp) (car tmp) tmp)))
          (when (not (eq prefix 'stop))
            (setq company-restclient-test-candidates-output
                  (mapcar (lambda (s) (substring-no-properties s))
                          (company-restclient 'candidates prefix)))))))

(Then "^company-restclient candidates are\\(?: \"\\(.*\\)\"\\|:\\)$"
      (lambda (expected)
        (should (equal company-restclient-test-candidates-output (read expected)))))

(Then "^company-restclient candidates contains\\(?: \"\\(.*\\)\"\\|:\\)$"
      (lambda (expected)
        (should (member expected company-restclient-test-candidates-output))))
