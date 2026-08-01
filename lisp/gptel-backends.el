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
    :host "127.0.0.1:8080"
    :protocol "http"
    :models (llm-setup-gptel-backends
             (cond ((string-match-p "clio" (system-name)) "clio")
                   ((string-match-p "hera" (system-name)) "hera")))))

(defun gptel-backends--omlx-models ()
  "Return text-generation oMLX instance names from the model registry."
  (cl-loop
   for model in llm-setup-models-list nconc
   (cl-loop
    for instance in (llm-setup-model-instances model)
    when
    (and
     (eq (llm-setup-model-kind model) 'text-generation)
     (eq (llm-setup-instance-provider instance) 'omlx))
    collect (llm-setup-get-instance-name model instance))))

(defun gptel-backends-omlx ()
  "Make a GPTel backend for models hosted by local oMLX."
  (gptel-make-openai "oMLX"
    :host "127.0.0.1:8000"
    :protocol "http"
    :endpoint "/v1/chat/completions"
    :models (gptel-backends--omlx-models)
    :key "dummy-key"))

(defun gptel-backends-perplexity ()
  "Make a GPTel backend for the direct Perplexity API."
  (gptel-make-openai "Perplexity"
    :host "api.perplexity.ai"
    :protocol "https"
    :endpoint "/chat/completions"
    :key (lambda () (auth-source-pass-get 'secret "api.perplexity.ai"))
    :models '(sonar-pro sonar-reasoning-pro sonar-deep-research)))

(defun gptel-backends-vibe-proxy ()
  "Make GPTel backends for models hosted on Clio."
  (gptel-make-openai "vibe-proxy"
    :host "127.0.0.1:8317"
    :protocol "http"
    :models '(claude-opus-4-7
              claude-opus-4-7-thinking-32000
              claude-sonnet-4-6
              claude-sonnet-4-6-thinking-32000)))

(defun gptel-backends-rinzler ()
  "Make GPTel backends for models hosted on Clio."
  (gptel-make-openai "rinzler"
    :host "127.0.0.1:63495"
    :protocol "http"
    :models '(llama31-metal))

  (gptel-make-openai "rinzler-andoria-t2"
    :host "andoria-t2:8088"
    :protocol "http"
    :models '(zai-org/GLM-4.7-Flash)))

;; (gptel-make-openai "rag-client"
;;   :host "127.0.0.1:8000"
;;   :protocol "http"
;;   :models '(
;;             Guidance-RAG
;;             ))

(provide 'gptel-backends)

;;; gptel-backends.el ends here
