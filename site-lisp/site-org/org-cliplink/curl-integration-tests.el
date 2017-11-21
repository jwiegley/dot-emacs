(require 'ert)

(add-to-list 'load-path ".")
(load "org-cliplink.el")

(setq org-cliplink-transport-implementation 'curl)
(setq org-cliplink-curl-transport-arguments '("--insecure"))

(ert-deftest org-cliplink-without-title--http ()
  (let ((url "http://127.0.0.1:8001/without-title.html")
        (expected-outcome "[[http://127.0.0.1:8001/without-title.html]]")
        (timeout 5))
    (with-temp-buffer
      (kill-new url)
      (org-cliplink)
      (sleep-for timeout)
      (should (equal (buffer-string) expected-outcome)))))

(ert-deftest org-cliplink-simple-title--http ()
  (let ((url "http://127.0.0.1:8001/http.html")
        (expected-outcome "[[http://127.0.0.1:8001/http.html][Hello World]]")
        (timeout 5))
    (with-temp-buffer
      (kill-new url)
      (org-cliplink)
      (sleep-for timeout)
      (should (equal (buffer-string) expected-outcome)))))

(ert-deftest org-cliplink-escape-title--http ()
  (let ((url "http://127.0.0.1:8001/html4-escaping.html")
        (expected-outcome "[[http://127.0.0.1:8001/html4-escaping.html][&{Hello} '{World} α  ]]")
        (timeout 5))
    (with-temp-buffer
      (kill-new url)
      (org-cliplink)
      (sleep-for timeout)
      (should (equal (buffer-string) expected-outcome)))))

(ert-deftest org-cliplink-simple-title--https ()
  (let ((url "https://127.0.0.1:4443/http.html")
        (expected-outcome "[[https://127.0.0.1:4443/http.html][Hello World]]")
        (timeout 5))
    (with-temp-buffer
      (kill-new url)
      (org-cliplink)
      (sleep-for timeout)
      (should (equal (buffer-string) expected-outcome)))))

(ert-deftest org-cliplink-simple-title--http-with-basic-auth ()
  (let ((url "http://127.0.0.1:8003/http.html")
        (expected-outcome "[[http://127.0.0.1:8003/http.html][Hello World]]")
        (timeout 5)
        (org-cliplink-secrets-path "./test-data/secrets/org-cliplink-basic-auth-it.el"))
    (with-temp-buffer
      (kill-new url)
      (org-cliplink)
      (sleep-for timeout)
      (should (equal (buffer-string) expected-outcome)))))

(ert-deftest org-cliplink-simple-title--https-with-basic-auth ()
  (let ((url "https://127.0.0.1:4445/http.html")
        (expected-outcome "[[https://127.0.0.1:4445/http.html][Hello World]]")
        (timeout 5)
        (org-cliplink-secrets-path "./test-data/secrets/org-cliplink-basic-auth-it.el"))
    (with-temp-buffer
      (kill-new url)
      (org-cliplink)
      (sleep-for timeout)
      (should (equal (buffer-string) expected-outcome)))))

(ert-run-tests-batch-and-exit)
