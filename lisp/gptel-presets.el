;;; gptel-presets --- Preset definitions for gptel -*- lexical-binding: t -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 28 Feb 2025
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
(require 'solar)
(require 'gptel)

(defconst gptel-presets-rewrite-use-remote t
  "Non-nil if we should use remote models (local is unavailable?).")

(defsubst gptel-presets-insert-no-think ()
  "Insert the text /no_think at the end of the user prompt."
  (insert " /no_think"))

(gptel-make-preset 'gpt
  :description "OpenAI's ChatGPT"
  ;; :backend "ChatGPT"
  ;; :model 'gpt-4.1
  :backend "LiteLLM"
  :model 'openai/gpt-4.1-2025-04-14
  :temperature 1.0)

(gptel-make-preset 'sonnet
  :description "Anthropic's Claude Sonnet, thinking"
  ;; :backend "Claude-thinking"
  ;; :model 'claude-sonnet-4-20250514
  :backend "LiteLLM"
  :model 'anthropic/claude-sonnet-4-20250514
  :temperature 1.0)

(gptel-make-preset 'opus
  :description "Anthropic's Claude Opus, thinking"
  ;; :backend "Claude-thinking"
  ;; :model 'claude-opus-4-20250514
  :backend "LiteLLM"
  :model 'anthropic/claude-opus-4-20250514
  :temperature 1.0)

(gptel-make-preset 'code
  :description "Best model for generating or interpreting code"
  :parents 'opus)

(gptel-make-preset 'qwen
  :description "Ali Baba's Qwen, thinking"
  ;; :backend "llama-swap-hera"
  ;; :model 'Qwen3-235B-A22B
  :backend "LiteLLM"
  :model 'hera/Qwen3-235B-A22B
  :temperature 1.0)

(gptel-make-preset 'r1
  :description "DeepSeek R1"
  ;; :backend "llama-swap-hera"
  ;; :model 'DeepSeek-R1-0528
  :backend "LiteLLM"
  :model 'hera/DeepSeek-R1-0528
  :temperature 0.6)

(gptel-make-preset 'r1q
  :description "DeepSeek R1, quick"
  ;; :backend "llama-swap-hera"
  ;; :model 'DeepSeek-R1-0528-Qwen3-8B
  :backend "LiteLLM"
  :model 'hera/DeepSeek-R1-0528-Qwen3-8B
  :temperature 0.6)

(gptel-make-preset 'web
  :description "Perplexity.ai sonar-pro"
  ;; :backend "Perplexity"
  ;; :model 'sonar-pro
  :backend "LiteLLM"
  :model 'perplexity/sonar-pro
  :request-params
  `(:web_search_options
    (:search_context_size
     "medium"
     :user_location
     (:latitude
      ,calendar-latitude
      :longitude
      ,calendar-longitude
      :country "US")))
  :include-reasoning 'ignore)

(gptel-make-preset 'deep
  :description "Perplexity.ai sonar-pro"
  ;; :backend "Perplexity"
  ;; :model 'sonar-pro
  :backend "LiteLLM"
  :model 'perplexity/sonar-pro
  :request-params
  `(:web_search_options
    (:search_context_size
     "high"
     :user_location
     (:latitude
      ,calendar-latitude
      :longitude
      ,calendar-longitude
      :country "US")))
  :include-reasoning 'ignore)

(gptel-make-preset 'think
  :description "Perplexity.ai sonar-reasoning-pro"
  ;; :backend "Perplexity"
  ;; :model 'sonar-reasoning-pro
  :backend "LiteLLM"
  :model 'perplexity/sonar-reasoning-pro
  :request-params
  `(:web_search_options
    (:search_context_size
     "high"
     :user_location
     (:latitude
      ,calendar-latitude
      :longitude
      ,calendar-longitude
      :country "US")))
  :include-reasoning 'ignore)

(gptel-make-preset 'research
  :description "Perplexity.ai deep reasoning"
  ;; :backend "Perplexity"
  ;; :model 'sonar-deep-research
  :backend "LiteLLM"
  :model 'perplexity/sonar-deep-research
  :request-params
  `(:web_search_options
    (:search_context_size
     "high"
     :user_location
     (:latitude
      ,calendar-latitude
      :longitude
      ,calendar-longitude
      :country "US")))
  :include-reasoning 'ignore)

(gptel-make-preset 'quick
  :post #'(lambda ()
            (add-hook 'gptel-prompt-transform-functions
                      #'gptel-presets-insert-no-think nil 'local)))

(gptel-make-preset 'rewrite
  :description "Model used for basic rewrites"
  :max-tokens 8192
  :include-reasoning nil
  :tools nil
  :parents `(quick
             ,(if gptel-presets-rewrite-use-remote
                  'sonnet
                'qwen)))

(gptel-make-preset 'default
  :description "Default setup"
  :parents 'qwen
  :system 'default
  :confirm-tool-calls 'auto
  :max-tokens 8192
  :use-context 'user
  :include-reasoning 'ignore)

(gptel-make-preset 'prompt
  :description "AI prompt refiner"
  :parents 'opus
  :system 'prompt
  :tools nil
  :max-tokens nil
  :include-reasoning 'ignore)

(gptel-make-preset 'persian
  :description "Persian translator"
  :parents 'opus
  :system 'persian
  :max-tokens 2048)

(gptel-make-preset 'spanish
  :description "Spanish translator"
  :parents 'opus
  :system 'spanish
  :max-tokens 2048)

(gptel-make-preset 'haskell
  :description "Expert Haskell coder"
  :parents 'opus
  :system 'haskell
  :max-tokens 1024)

(gptel-make-preset 'shorten
  :description "Shorten Org-mode titles"
  :rewrite-directive 'shorten
  :rewrite-message "Shorten it as described."
  :parents 'rewrite)

(gptel-make-preset 'title
  :description "Create Org-mode title"
  :system 'title
  :parents 'rewrite)

(gptel-make-preset 'proof
  :description "Proofread and spell-checking"
  :rewrite-directive 'proofread
  :rewrite-message "Proofread as instructed."
  :parents 'rewrite)

(gptel-make-preset 'docstring
  :description "Add missing Emacs Lisp docstrings"
  :rewrite-directive 'emacs
  :rewrite-message
  (concat "Rewrite: Add informative docstrings for all functions that are"
          " missing documentation. Only add the documentation, do not"
          " remove any code. Preserve all existing code as is, simply edit"
          " the text to insert the missing docstring. Do not provide any"
          " rationale or explanation, and do not enclose any of the existing"
          " code within progn blocks.")
  :parents 'rewrite)

(provide 'gptel-presets)

;;; gptel-presets.el ends here
