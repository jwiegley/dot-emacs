;;; gptel-backends --- Definitions of GPTel backends -*- lexical-binding: t -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 18 Jun 2025
;; Version: 1.0
;; Keywords: ai gptel tools
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;;; Code:

(require 'cl-lib)
(require 'gptel-request)
;; (require 'gptel-kagi)
;; (require 'gptel-ollama)
;; (require 'gptel-gemini)
(require 'gptel-openai)
(require 'gptel-openai-extras)
(require 'auth-source-pass)
;; (require 'gptel-anthropic)
(require 'llm-setup)

(defconst gptel-curl--common-args
  '("--location"
    "--silent"
    "--insecure"
    "--compressed"
    "--speed-limit" "1"
    "--speed-time" "7200"
    "--max-time" "7200"
    "-XPOST"
    "-D-")
  "Arguments always passed to Curl for gptel queries.")

(defun gptel-backends-llama-swap ()
  "Make GPTel backends for models hosted on Clio."
  (gptel-make-openai "llama-swap"
    :host (llm-setup-host-policy "llmSetup" "gptelEndpoints" "llamaSwap")
    :protocol "http"
    :models (llm-setup-gptel-backends
             (let ((host (llm-setup-host-policy "currentHost")))
               (and (member host llm-setup-valid-hostnames) host)))))

(defun gptel-backends--omlx-models ()
  "Return text-generation oMLX models available on the current host."
  (let ((hostname (llm-setup-host-policy "currentHost")))
    (cl-loop
     for model in llm-setup-models-list nconc
     (cl-loop
      for instance in (llm-setup-model-instances model)
      when
      (and
       (eq (llm-setup-model-kind model) 'text-generation)
       (eq (llm-setup-instance-provider instance) 'omlx))
      nconc
      (llm-setup-get-instance-gptel-backend model instance hostname)))))

(defun gptel-backends-omlx ()
  "Make a GPTel backend for models hosted by local oMLX."
  (gptel-make-openai "oMLX"
    :host (llm-setup-host-policy "llmSetup" "gptelEndpoints" "omlx")
    :protocol "http"
    :endpoint "/v1/chat/completions"
    :models (gptel-backends--omlx-models)
    :key "dummy-key"))

(defun gptel-backends-perplexity ()
  "Make a GPTel backend for the direct Perplexity API."
  (gptel-make-openai "Perplexity"
    :host (llm-setup-host-policy "llmSetup" "gptelEndpoints" "perplexity")
    :protocol "https"
    :endpoint "/chat/completions"
    :key (lambda () (auth-source-pass-get 'secret "api.perplexity.ai"))
    :models (llm-setup-policy-symbols "emacs" "providerModels" "perplexity")))

(defun gptel-backends-vibe-proxy ()
  "Make GPTel backends for models hosted on Clio."
  (gptel-make-openai "vibe-proxy"
    :host (llm-setup-host-policy "llmSetup" "gptelEndpoints" "vibeProxy")
    :protocol "http"
    :key (lambda () (auth-source-pass-get 'secret "vibe-proxy"))
    :models (llm-setup-policy-symbols "emacs" "providerModels" "vibe-proxy")))

(defun gptel-backends-rinzler ()
  "Make GPTel backends for Rinzler models."
  (gptel-make-openai "rinzler"
    :host (llm-setup-host-policy "llmSetup" "gptelEndpoints" "rinzler")
    :protocol "http"
    :models (llm-setup-policy-symbols "emacs" "providerModels" "rinzler"))

  (gptel-make-openai "rinzler-andoria-t2"
    :host (llm-setup-host-policy "llmSetup" "gptelEndpoints" "rinzlerAndoria")
    :protocol "http"
    :models (llm-setup-policy-symbols "emacs" "providerModels" "rinzler-andoria")))

(defun gptel-backends-hermes ()
  "Make GPTel backends for Hermes Agent on Vulcan."
  (gptel-make-openai "hermes"
    :host (llm-setup-host-policy "llmSetup" "gptelEndpoints" "hermes")
    :protocol "https"
    :key (lambda () (auth-source-pass-get 'secret "api.hermes.com"))
    :models (llm-setup-policy-symbols "emacs" "providerModels" "hermes")))

;; (gptel-make-openai "rag-client"
;;   :host "127.0.0.1:8000"
;;   :protocol "http"
;;   :models '(
;;             Guidance-RAG
;;             ))

(provide 'gptel-backends)

;;; gptel-backends.el ends here
