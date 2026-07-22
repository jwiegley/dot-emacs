;;; gptel-backends-test.el --- Tests for gptel-backends  -*- lexical-binding: t; -*-

;;; Commentary:

;; Regression tests for registry-backed GPTel model selection.

;;; Code:

(require 'cl-lib)
(require 'ert)
(require 'gptel-backends)

(ert-deftest gptel-backends-test-omlx-models-follow-registry ()
  "Expose every text-generation oMLX instance and no stale entries."
  (let* ((models
          (gptel-backend-models (gptel-backends-omlx)))
         (instances (llm-setup-instances-list))
         (registry-models
          (cl-loop
           for (model . instance) in instances
           when
           (and
            (eq (llm-setup-model-kind model) 'text-generation)
            (eq (llm-setup-instance-provider instance) 'omlx))
           collect (llm-setup-get-instance-name model instance))))
    (should-not (memq 'Qwen3.6-35B-A3B-UD-MLX-4bit models))
    (dolist (name '(deepseek-ai-DeepSeek-V4-Flash-8bit
                    Qwen3.6-27B-oQ4e-mtp
                    Qwen3.6-27B-oQ8-mtp
                    Qwen3.6-35B-A3B-oQ4-mtp))
      (should (memq name models)))
    (should (equal models registry-models))
    (dolist (name models)
      (should
       (cl-some
        (lambda (entry)
          (let ((model (car entry))
                (instance (cdr entry)))
            (and
             (eq name (llm-setup-get-instance-name model instance))
             (eq (llm-setup-model-kind model) 'text-generation)
             (eq (llm-setup-instance-provider instance) 'omlx))))
        instances)))))

(provide 'gptel-backends-test)

;;; gptel-backends-test.el ends here
