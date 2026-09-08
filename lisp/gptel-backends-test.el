;;; gptel-backends-test.el --- Tests for gptel-backends  -*- lexical-binding: t; -*-

;;; Commentary:

;; Regression tests for registry-backed GPTel model selection.

;;; Code:

(require 'cl-lib)
(require 'ert)
(require 'gptel-backends)

(ert-deftest gptel-backends-test-omlx-models-follow-current-host ()
  "Expose only text-generation oMLX instances hosted on the current host."
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
             :name 'embedding-model :provider 'omlx :hostnames '("hera")))))))
    (cl-letf (((symbol-function 'llm-setup-host-policy)
               (lambda (&rest keys)
                 (cond
                  ((equal keys '("currentHost")) "hera")
                  ((equal keys '("llmSetup" "gptelEndpoints" "omlx"))
                   "127.0.0.1:8000")))))
      (should
       (equal (gptel-backend-models (gptel-backends-omlx))
              '(hera-model))))))

(provide 'gptel-backends-test)

;;; gptel-backends-test.el ends here
