;;; -*- lexical-binding: t -*-

(ert-deftest org-cliplink-curl-prepare-response-buffer-name ()
  (let ((url "http://rexim.me/"))
    (should (string-match " \\*curl-rexim.me-[a-z0-9]+"
                          (org-cliplink-curl-prepare-response-buffer-name url)))))

(ert-deftest org-cliplink-credentials-to-basic-auth-test ()
  (should (equal "Basic aGVsbG86d29ybGQ="
                 (org-cliplink-credentials-to-basic-auth "hello" "world"))))

(ert-deftest org-cliplink-build-curl-arguments-test ()
  (let* ((url "http://rexim.me")
         (username "rexim")
         (password "nyasha")
         (extra-arguments (list "--secure"))
         (expected-output (list "--secure"
                                "--include"
                                "--silent"
                                "--show-error"
                                "-X" "GET"
                                "--user"
                                (concat username ":" password)
                                url)))
    (should (equal expected-output
                   (org-cliplink-build-curl-arguments url
                                                      (list :username username
                                                            :password password)
                                                      extra-arguments)))))

(ert-deftest org-cliplink-build-curl-sentinel-test ()
  (let* ((process 42)
         (callback-invoked nil)
         (response-buffer-name "khooy"))
    (with-mock
     (mock (process-live-p 42) => nil)
     (mock (process-exit-status 42) => 0)
     (mock (curl-sentinel-callback-mock nil) => nil :times 1)
     (let ((sentinel (org-cliplink-build-curl-sentinel
                      response-buffer-name
                      #'curl-sentinel-callback-mock)))
       (generate-new-buffer response-buffer-name)
       (funcall sentinel process nil)))
    (with-mock
     (mock (process-live-p 42) => nil)
     (mock (process-exit-status 42) => 1)
     (not-called curl-sentinel-callback-mock)
     (let ((sentinel (org-cliplink-build-curl-sentinel
                      response-buffer-name
                      #'curl-sentinel-callback-mock)))
       (generate-new-buffer response-buffer-name)
       (should-error (funcall sentinel process nil)
                     :type 'error)))))

(ert-deftest org-cliplink-shadow-basic-auth-credentials-test ()
  (should (not (org-cliplink-shadow-basic-auth-credentials nil)))
  (should (equal (list :username "***"
                       :password "***")
                 (org-cliplink-shadow-basic-auth-credentials t))))

(ert-deftest org-cliplink-start-curl-process-test ()
  (with-mock
   (mock (start-process "curl" "khooy" * "foo" "bar" "buzz") => 42 :times 1)
   (should (equal 42
                  (org-cliplink-start-curl-process "khooy" '("foo" "bar" "buzz"))))))

(ert-deftest org-cliplink-log-curl-command-test ()
  (with-mock
   (mock (message "curl %s"
                  (concat "--hello --world "
                          "--include --silent --show-error "
                          "-X GET --user ***:*** http://rexim.me"))
         => 42
         :times 1)
   (should
    (equal
     42
     (org-cliplink-log-curl-command
      "http://rexim.me"
      (list :username "hello" :password "world")
      (list "--hello" "--world"))))))
