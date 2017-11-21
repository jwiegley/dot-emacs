(ert-deftest org-cliplink-parse-raw-header-test ()
  (should (equal
           '(("Last-Modified" . "Sun, 08 Mar 2015 14:06:08 GMT")
             ("Content-Length" . "199")
             ("Content-type" . "text/html")
             ("Date" . "Sun, 08 Mar 2015 14:17:14 GMT")
             ("Server" . "SimpleHTTP/0.6 Python/2.7.9"))
           (org-cliplink-parse-raw-header
            (concat "HTTP/1.0 200 OK\n"
                    "Server: SimpleHTTP/0.6 Python/2.7.9\n"
                    "Date: Sun, 08 Mar 2015 14:17:14 GMT\n"
                    "Content-type: text/html\n"
                    "Content-Length: 199\n"
                    "Last-Modified: Sun, 08 Mar 2015 14:06:08 GMT\n"))))
  (should (equal
           '(("Last-Modified" . "Sun, 08 Mar 2015 14:06:08 GMT")
             ("Content-Length" . "199")
             ("Content-type" . "text/html")
             ("Date" . "Sun, 08 Mar 2015 14:17:14 GMT")
             ("Server" . "SimpleHTTP/0.6 Python/2.7.9"))
           (org-cliplink-parse-raw-header
            (concat "HTTP/1.0 200 OK\n"
                    "Server: SimpleHTTP/0.6 Python/2.7.9\r\n"
                    "Date: Sun, 08 Mar 2015 14:17:14 GMT\n"
                    "Content-type: text/html\n"
                    "Content-Length: 199\r\n"
                    "Last-Modified: Sun, 08 Mar 2015 14:06:08 GMT\n")))))

(ert-deftest org-cliplink-parse-response-test ()
  (with-mock
   (stub org-cliplink-parse-raw-header => nil)
   (let ((test-data '(("test-data/responses/inconsistent-eol-response" .
                       (nil . "Here goes body\n"))
                      ("test-data/responses/correct-response-without-title" .
                       (nil . "Here goes body\n")))))
     (dolist (test-case test-data)
       (message (car test-case))
       (let ((data-file (car test-case))
             (expected-outcome (cdr test-case)))
         (with-temp-buffer
           (insert-file data-file)
           (should (equal (org-cliplink-parse-response) expected-outcome))))))))


(ert-deftest org-cliplink-read-secrets-test ()
  (let ((org-cliplink-secrets-path "./test-data/secrets/org-cliplink-secrets.el"))
    (should (equal (org-cliplink-read-secrets)
                   '(:hello (1 2 3)))))
  (let ((org-cliplink-secrets-path "/path/to/non/existing/secrets"))
    (should (not (org-cliplink-read-secrets)))))

(ert-deftest org-cliplink-check-basic-auth-for-url-test ()
  (let ((org-cliplink-secrets-path "./test-data/secrets/org-cliplink-basic-auth-secrets.el"))
    (should (equal (org-cliplink-check-basic-auth-for-url "http://rexim.me/test")
                   '(:url-pattern "http://rexim.me/*" :username "horta" :password "hell")))
    (should (not (org-cliplink-check-basic-auth-for-url "http://fornever.me/test")))))

(ert-deftest org-cliplink-extract-and-prepare-title-from-current-buffer-test ()
  (with-mock
   (stub org-cliplink-parse-response =>
         '(nil . "<title>hello</title>"))
   (not-called org-cliplink-uncompress-gziped-text)
   (should (equal "hello"
                  (org-cliplink-extract-and-prepare-title-from-current-buffer))))

  (with-mock
   (stub org-cliplink-parse-response =>
         '((("Content-Encoding" . "gzip")) . "<title>hello</title>"))
   (stub org-cliplink-uncompress-gziped-text =>
         "<title>hello</title>")
   (should (equal "hello"
                  (org-cliplink-extract-and-prepare-title-from-current-buffer)))))

(ert-deftest org-cliplink-escape-html4-test ()
  (should (equal "&{Hello} '{World} α  "
                 (org-cliplink-escape-html4
                  "&amp;[Hello] &#39;[World] &alpha; &nbsp;")))
  (should (not (org-cliplink-escape-html4 nil))))

(ert-deftest org-cliplink-insert-org-mode-link-callback-test ()
  (with-temp-buffer
    (org-cliplink-insert-org-mode-link-callback "http://google.com/" "Google")
    (should (equal (buffer-string) "[[http://google.com/][Google]]")))

  (with-temp-buffer
    (org-cliplink-insert-org-mode-link-callback "http://google.com" nil)
    (should (equal (buffer-string) "[[http://google.com]]"))))

(ert-deftest org-cliplink-uncompress-gziped-text-test ()
  (let ((gziped-content (concat "\x1F\x8B\x08\x00\xD8\x8B"
                                "\x74\x55\x00\x03\xCB\x48"
                                "\xCD\xC9\xC9\x57\x28\xCF"
                                "\x2F\xCA\x49\x01\x00\x85"
                                "\x11\x4A\x0D\x0B\x00\x00"
                                "\x00")))
    (should (equal "hello world"
                   (org-cliplink-uncompress-gziped-text gziped-content)))))

(ert-deftest org-cliplink-clipboard-content-test ()
  (kill-append "khooy" nil)
  (should (equal "khooy"
                 (org-cliplink-clipboard-content))))
