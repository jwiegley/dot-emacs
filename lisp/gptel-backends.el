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

(require 'gptel-request)
;; (require 'gptel-kagi)
;; (require 'gptel-ollama)
;; (require 'gptel-gemini)
(require 'gptel-openai)
(require 'gptel-openai-extras)
;; (require 'gptel-anthropic)
(require 'hf)

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

(defun gptel-backends-make-litellm ()
  "Make GPTel backends for LiteLLM hosted models."
  (gptel-make-openai "LiteLLM"
    :host "litellm.vulcan.lan"
    :protocol "https"
    :endpoint "/v1/chat/completions"
    :key gptel-api-key
    :models (hf-gptel-backends)
    :header
    (lambda () (when-let* ((key (gptel--get-api-key)))
            `(("x-api-key"         . ,key)
              ("x-litellm-timeout" . "7200")
              ("x-litellm-tags"    . "gptel")
              ("anthropic-version" . "2023-06-01")
              ("anthropic-beta"    . "pdfs-2024-09-25")
              ("anthropic-beta"    . "output-128k-2025-02-19")
              ("anthropic-beta"    . "prompt-caching-2024-07-31"))))))

(defun gptel-backends-llama-swap ()
  "Make GPTel backends for models hosted on Clio."
  (gptel-make-openai "llama-swap"
    :host "127.0.0.1:8080"
    :protocol "http"
    :models (hf-gptel-backends
             (cond ((string-match-p "clio" (system-name)) "clio")
                   ((string-match-p "hera" (system-name)) "hera")))))

(defun gptel-backends-vibe-proxy ()
  "Make GPTel backends for models hosted on Clio."
  (gptel-make-openai "vibe-proxy"
    :host "127.0.0.1:8317"
    :protocol "http"
    :models '(claude-opus-4-6
              claude-opus-4-6-thinking-32000)))

(defun gptel-backends-rinzler ()
  "Make GPTel backends for models hosted on Clio."
  (gptel-make-openai "rinzler"
    :host "127.0.0.1:9998"
    :protocol "http"
    :models '(llama-3.2-3b-instruct-fast-tp2)))

;; (gptel-make-openai "rag-client"
;;   :host "127.0.0.1:8000"
;;   :protocol "http"
;;   :models '(
;;             Guidance-RAG
;;             ))

(provide 'gptel-backends)

;;; gptel-backends.el ends here
