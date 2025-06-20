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
(require 'gptel)

(use-package gptel-curl
  :config
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
    "Arguments always passed to Curl for gptel queries."))

;; (use-package gptel-kagi
;;   :config
;;   (gptel-make-kagi "Kagi"
;;     :key gptel-api-key
;;     :models '(
;;               fastgpt
;;               )))

;; (use-package gptel-ollama
;;   :config
;;   (gptel-make-ollama "Ollama"
;;     :host "localhost:11434"
;;     :protocol "http"
;;     :request-params '(:options (:num_ctx 8192))
;;     :models
;;     '(
;;       HammerAI/midnight-miqu-70b-v1.5:latest
;;       beezu/Midnight-Miqu-103B-v1.5:latest
;;       datacrystals/midnight-rose103b-v2:latest
;;       datacrystals/miqulitz120b-v2:latest

;; (use-package gptel-gemini
;;   :config
;;   (gptel-make-gemini "Gemini"
;;     :key gptel-api-key
;;     ))

(use-package gptel-openai
  :config
  (unless t
    (gptel-make-openai "ChatGPT"
      :key gptel-api-key
      :models '(
                (gpt-4.1-2025-04-14
                 :description "Flagship GPT model for complex tasks"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (gpt-4.1-mini-2025-04-14
                 :description "Balanced for intelligence, speed, and cost"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (gpt-4.1-nano-2025-04-14
                 :description "Fastest, most cost-effective GPT-4.1 model"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (gpt-4o-2024-08-06
                 :description "Fast, intelligent, flexible GPT model"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (gpt-4o-audio-preview-2024-12-17
                 :description "GPT-4o models capable of audio inputs and outputs"
                 :capabilities (media tool json url)
                 :mime-types ("audio/mpeg" "audio/mp4"))
                (gpt-4o-mini-2024-07-18
                 :description "Fast, affordable small model for focused tasks"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (gpt-4o-mini-audio-preview-2024-12-17
                 :description "Smaller model capable of audio inputs and outputs"
                 :capabilities (media tool json url)
                 :mime-types ("audio/mpeg" "audio/mp4"))
                (o3-2025-04-16
                 :description "Our most powerful reasoning model"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (o3-mini-2025-01-31
                 :description "A small model alternative to o3"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (o3-pro-2025-06-10
                 :description "Version of o3 with more compute for better responses"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (o4-mini-2025-04-16
                 :description "Faster, more affordable reasoning model"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                )))

  (unless t
    (gptel-make-openai "Groq"
      :host "api.groq.com"
      :endpoint "/openai/v1/chat/completions"
      :key gptel-api-key
      :models '(
                compound-beta
                deepseek-r1-distill-llama-70b
                llama-3.3-70b-versatile
                meta-llama/Llama-Guard-4-12B
                meta-llama/llama-4-maverick-17b-128e-instruct
                meta-llama/llama-4-scout-17b-16e-instruct
                qwen-qwq-32b
                )))

  (unless t
    (gptel-make-openai "OpenRouter"
      :host "openrouter.ai"
      :endpoint "/api/v1/chat/completions"
      :key gptel-api-key
      :models '(
                deepseek/deepseek-r1-0528:free
                meta-llama/llama-4-maverick:free
                qwen/qwen3-235b-a22b:free
                )))

  ;; (gptel-make-openai "lmstudio"
  ;;   :host "127.0.0.1:1234"
  ;;   :protocol "http"
  ;;   :models '(
  ;;             ))

  ;; (gptel-make-openai "rag-client"
  ;;   :host "127.0.0.1:8000"
  ;;   :protocol "http"
  ;;   :models '(
  ;;             Guidance-RAG
  ;;             ))

  (unless t
    (gptel-make-openai "llama-cpp"
      :host "127.0.0.1:8081"
      :protocol "http"
      :models '(
                Qwen3-30B-A3B
                )))

  (defun gptel-backends-make-litellm ()
    (gptel-make-openai "LiteLLM"
      :host "vulcan"
      :protocol "http"
      :endpoint "/litellm/v1/chat/completions"
      :key gptel-api-key
      :models '(
                (hera/DeepSeek-R1-0528
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/DeepSeek-R1-0528-Qwen3-8B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/DeepSeek-V3-0324
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Llama-3.3-Nemotron-Super-49B-v1
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Llama-4-Maverick-17B-128E-Instruct
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Llama-4-Scout-17B-16E-Instruct
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Mistral-Nemo-Instruct-2407
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Phi-4-reasoning-plus
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/QwQ-32B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen.Qwen3-Reranker-8B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen3-0.6B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen3-1.7B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen3-14B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen3-235B-A22B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen3-30B-A3B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen3-32B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen3-4B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen3-8B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/Qwen3-Embedding-8B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/WizardCoder-Python-34B-V1.0
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/WizardCoder-Python-7B-V1.0
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/agentica-org/DeepCoder-1.5B-Preview
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/agentica-org/DeepCoder-14B-Preview
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/bge-m3
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/gemma-3-27b-it
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/meta-llama/Llama-4-Scout-17B-16E-Instruct
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/microsoft/phi-4
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/mistralai/Codestral-22B-v0.1
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/mistralai/Mistral-Small-Instruct-2409
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/mlx-community/Llama-4-Maverick-17B-128E-Instruct-6bit
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/mlx-community/MiMo-7B-RL-4bit
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/mlx-community/whisper-large-v3-mlx
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/nomic-embed-text-v2-moe
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/nvidia/NV-Embed-v2
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/nvidia/OpenCodeReasoning-Nemotron-32B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/open-thoughts/OpenThinker2-32B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/r1-1776-distill-llama-70b
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (hera/sentence-transformers/all-MiniLM-L6-v2
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))

                (athena/Llama-3.3-Nemotron-Super-49B-v1
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (athena/Qwen/QwQ-32B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (athena/Qwen3-30B-A3B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (athena/Qwen3-32B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (athena/WizardCoder-Python-34B-V1.0
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))

                (clio/DeepSeek-R1-0528-Qwen3-8B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/Mistral-Nemo-Instruct-2407
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/Phi-4-reasoning-plus
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/Qwen3-0.6B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/Qwen3-1.7B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/Qwen3-14B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/Qwen3-30B-A3B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/Qwen3-32B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/Qwen3-4B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/Qwen3-8B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/WizardCoder-Python-7B-V1.0
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (clio/gemma-3-27b-it
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))

                (openai/gpt-4.1-2025-04-14
                 :description "Flagship GPT model for complex tasks"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/gpt-4.1-mini-2025-04-14
                 :description "Balanced for intelligence, speed, and cost"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/gpt-4.1-nano-2025-04-14
                 :description "Fastest, most cost-effective GPT-4.1 model"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/gpt-4o-2024-08-06
                 :description "Fast, intelligent, flexible GPT model"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/gpt-4o-audio-preview-2024-12-17
                 :description "GPT-4o models capable of audio inputs and outputs"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/gpt-4o-mini-2024-07-18
                 :description "Fast, affordable small model for focused tasks"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/gpt-4o-mini-audio-preview-2024-12-17
                 :description "Smaller model capable of audio inputs and outputs"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/o3-2025-04-16
                 :description "Our most powerful reasoning model"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/o3-mini-2025-01-31
                 :description "A small model alternative to o3"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/o3-pro-2025-06-10
                 :description "Version of o3 with more compute for better responses"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openai/o4-mini-2025-04-16
                 :description "Faster, more affordable reasoning model"
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))

                (anthropic/claude-opus-4-20250514
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (anthropic/claude-sonnet-4-20250514
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (anthropic/claude-3-5-haiku-20241022
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))

                (perplexity/sonar-pro
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (perplexity/sonar-reasoning-pro
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (perplexity/sonar-deep-research
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (perplexity/r1-1776
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))

                (groq/compound-beta
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (groq/deepseek-r1-distill-llama-70b
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (groq/llama-3.3-70b-versatile
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (groq/meta-llama/Llama-Guard-4-12B
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (groq/meta-llama/llama-4-maverick-17b-128e-instruct
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (groq/meta-llama/llama-4-scout-17b-16e-instruct
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (groq/qwen-qwq-32b
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))

                (openrouter/deepseek/deepseek-r1-0528:free
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openrouter/meta-llama/llama-4-maverick:free
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                (openrouter/qwen/qwen3-235b-a22b:free
                 :description ""
                 :capabilities (media tool json url)
                 :mime-types ("image/jpeg" "image/png" "image/gif" "image/webp"))
                )
      :header
      (lambda () (when-let* ((key (gptel--get-api-key)))
              `(("x-api-key"         . ,key)
                ("x-litellm-timeout" . "7200")
                ("x-litellm-tags"    . "gptel")
                ("anthropic-version" . "2023-06-01")
                ("anthropic-beta"    . "pdfs-2024-09-25")
                ("anthropic-beta"    . "output-128k-2025-02-19")
                ("anthropic-beta"    . "prompt-caching-2024-07-31"))))))

  ;; (gptel-make-openai "mlx-lm"
  ;;   :host "192.168.50.5:9090"
  ;;   :protocol "http"
  ;;   :models '(
  ;;             ))

  (defun gptel-backends-make-clio (&rest models)
    (gptel-make-openai "llama-swap-clio"
      :host
      (if (string-match-p "\\<[Cc]lio\\>" system-name)
          "127.0.0.1:8080"
        (if (string-match-p "\\<[Hh]era\\>" system-name)
            "192.168.2.2:8080"
          "192.168.50.112:8080"))
      :protocol "http"
      :models models))

  (defun gptel-backends-make-athena (&rest models)
    (gptel-make-openai "llama-swap-athena"
      :host
      (if (string-match-p "\\<[Aa]thena\\>" system-name)
          "127.0.0.1:8080"
        "192.168.50.235:8080")
      :protocol "http"
      :models models))

  (defun gptel-backends-make-hera (&rest models)
    (gptel-make-openai "llama-swap-hera"
      :host
      (if (string-match-p "\\<[Hh]era\\>" system-name)
          "127.0.0.1:8080"
        "192.168.50.5:8443")
      :protocol
      (if (string-match-p "\\<[Hh]era\\>" system-name)
          "http"
        "https")
      :models models)))

(unless t
  (use-package gptel-openai-extras
    :config
    (gptel-make-perplexity "Perplexity"
      :key gptel-api-key
      :models '(
                sonar-pro
                sonar-reasoning-pro
                sonar-deep-research
                r1-1776
                )
      :request-params
      `(:web_search_options
        (:search_context_size
         "high"
         :user_location
         (:latitude
          ,calendar-latitude
          :longitude
          ,calendar-longitude
          :country "US"))))))

(unless t
  (use-package gptel-anthropic
    :config
    (gptel-make-anthropic "Claude"
      :key gptel-api-key
      :models '(
                claude-opus-4-20250514
                claude-sonnet-4-20250514
                claude-3-5-haiku-20241022
                ))

    (gptel-make-anthropic "Claude-thinking" ;Any name you want
      :key gptel-api-key
      :models '(
                claude-opus-4-20250514
                claude-sonnet-4-20250514
                )
      :header
      (lambda () (when-let* ((key (gptel--get-api-key)))
              `(("x-api-key" . ,key)
                ("anthropic-version" . "2023-06-01")
                ("anthropic-beta" . "pdfs-2024-09-25")
                ("anthropic-beta" . "output-128k-2025-02-19")
                ("anthropic-beta" . "prompt-caching-2024-07-31"))))
      :request-params '(:thinking
                        (:type "enabled"
                               :budget_tokens 8192)
                        :max_tokens 16384))))

(provide 'gptel-backends)

;;; gptel-backends.el ends here
