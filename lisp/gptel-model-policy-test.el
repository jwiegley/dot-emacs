;;; gptel-model-policy-test.el --- Managed GPTel policy tests -*- lexical-binding: t; -*-

;;; Commentary:

;; Run with the packaged GPTel library and NIX_MODEL_POLICY_FILE pointing at
;; generated model policy.  These tests register backends but send no requests.

;;; Code:

(require 'ert)
(defvar llm-setup-policy-file
  (or (getenv "NIX_MODEL_POLICY_FILE")
      (error "NIX_MODEL_POLICY_FILE must name the generated test policy")))
(defvar llm-setup-host-policy-file
  (or (getenv "NIX_HOST_POLICY_FILE")
      (error "NIX_HOST_POLICY_FILE must name the generated test policy")))
(defvar llm-setup-default-hostname "hera")
(defvar llm-setup-local-hostname "clio")
(defvar llm-setup-valid-hostnames '("hera" "clio"))
(require 'llm-setup)
(require 'gptel-presets)
(require 'gptel-backends)

(ert-deftest gptel-model-policy-presets ()
  "Register model choices, parameters and role parents from Nix."
  (maphash
   (lambda (name model)
     (should (equal (symbol-name (plist-get (gptel-get-preset (intern name)) :model))
                    model)))
   (llm-setup-policy "emacs" "presets"))
  (maphash
   (lambda (name parents)
     ;; The commit-summary preset is defined by gptel-ext, not this module.
     (unless (equal name "commit-summary")
       (should (equal (plist-get (gptel-get-preset (intern name)) :parents)
                      (mapcar #'intern parents)))))
   (llm-setup-policy "emacs" "parents"))
  (dolist (name '(gpt opus sonnet haiku opus-max sonnet-max))
    (should (= (plist-get (gptel-get-preset name) :temperature)
               (llm-setup-policy "emacs" "temperature"))))
  (should (eq (plist-get (gptel-get-preset 'qwen) :model)
              (llm-setup-default-model-name)))
  (should (= (plist-get
              (plist-get (plist-get (gptel-get-preset 'high-output) :request-params)
                         :merge)
              :max_tokens)
             (llm-setup-policy "emacs" "highOutputTokens"))))

(ert-deftest gptel-model-policy-applied-role ()
  "Apply the configured rewrite role through GPTel's real preset machinery."
  (let ((parent (car (llm-setup-policy "emacs" "parents" "rewrite"))))
    (gptel-with-preset 'rewrite
      (should (equal (symbol-name gptel-model)
                     (llm-setup-policy "emacs" "presets" parent))))))

(ert-deftest gptel-model-policy-backends ()
  "Register the managed model inventory without consulting credential stores."
  (cl-letf (((symbol-function 'auth-source-pass-get)
             (lambda (&rest _args) (error "Unexpected credential lookup")))
            ((symbol-function 'url-retrieve)
             (lambda (&rest _args) (error "Unexpected network request")))
            ((symbol-function 'url-retrieve-synchronously)
             (lambda (&rest _args) (error "Unexpected network request"))))
    (gptel-backends-perplexity)
    (gptel-backends-vibe-proxy)
    (gptel-backends-rinzler)
    (gptel-backends-hermes)
    (dolist (entry '(("vibeProxy" . "vibe-proxy")
                     ("rinzler" . "rinzler")
                     ("rinzlerAndoria" . "rinzler-andoria-t2")
                     ("hermes" . "hermes")))
      (should (equal (gptel-backend-host (gptel-get-backend (cdr entry)))
                     (llm-setup-host-policy "llmSetup" "gptelEndpoints" (car entry)))))
    (dolist (entry '(("perplexity" . "Perplexity")
                     ("vibe-proxy" . "vibe-proxy")
                     ("rinzler" . "rinzler")
                     ("rinzler-andoria" . "rinzler-andoria-t2")
                     ("hermes" . "hermes")))
      (should
       (equal
        (mapcar #'symbol-name
                (gptel-backend-models (gptel-get-backend (cdr entry))))
        (llm-setup-policy "emacs" "providerModels" (car entry)))))))

(provide 'gptel-model-policy-test)
;;; gptel-model-policy-test.el ends here
