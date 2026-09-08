;;; gptel-backends-test.el --- Tests for gptel-backends  -*- lexical-binding: t; -*-

;;; Commentary:

;; Regression tests for registry-backed GPTel model selection.

;;; Code:

(require 'cl-lib)
(require 'ert)
(require 'gptel-backends)

(ert-deftest gptel-backends-test-omlx-models-follow-host-access-policy ()
  "Expose local models everywhere and Hera models from Clio."
  (let ((llm-setup-models-list
         (list
          (make-llm-setup-model
           :name 'fixture
           :instances
           (list
            (make-llm-setup-instance
             :name 'hera-model :provider 'omlx :hostnames '("hera"))
            (make-llm-setup-instance
             :name 'clio-model :provider 'omlx :hostnames '("clio"))))
          (make-llm-setup-model
           :name 'embedding
           :kind 'embedding
           :instances
           (list
            (make-llm-setup-instance
             :name 'embedding-model :provider 'omlx :hostnames '("hera"))))))
        current-host
        calls)
    (cl-letf
        (((symbol-function 'llm-setup-host-policy)
          (lambda (&rest keys)
            (cond
             ((equal keys '("currentHost")) current-host)
             ((equal keys (list "llmSetup" "gptelOmlxHosts" current-host))
              (if (equal current-host "clio") '("clio" "hera") '("hera")))
             ((equal keys '("llmSetup" "gptelEndpoints" "omlx"))
              "127.0.0.1:8000")
             ((equal keys '("llmSetup" "gptelEndpoints" "omlxRemote" "hera"))
              "hera.lan:8443"))))
         ((symbol-function 'gptel-make-openai)
          (lambda (name &rest args)
            (let ((backend
                   (list name
                         (plist-get args :host)
                         (plist-get args :protocol)
                         (mapcar #'car (plist-get args :models)))))
              (push backend calls)
              backend))))
      (setq current-host "hera"
            calls nil)
      (should (equal (gptel-backends-omlx)
                     '("oMLX" "127.0.0.1:8000" "http" (hera-model))))
      (should (equal (nreverse calls)
                     '(("oMLX" "127.0.0.1:8000" "http" (hera-model)))))

      (setq current-host "clio"
            calls nil)
      (should (equal (gptel-backends-omlx)
                     '("oMLX" "127.0.0.1:8000" "http" (clio-model))))
      (should
       (equal
        (nreverse calls)
        '(("oMLX" "127.0.0.1:8000" "http" (clio-model))
          ("oMLX-hera" "hera.lan:8443" "https" (hera-model))))))))

(provide 'gptel-backends-test)

;;; gptel-backends-test.el ends here
