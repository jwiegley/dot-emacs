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

(defmacro my/gptel-make-preset (name &rest keys)
  "Porcelain around `gptel-make-preset' of NAME, to help manage `:post'.
The KEYS argument is the same as `gptel-make-preset', except that two
new keys are specially supported:

  :request-params (PARAMETERS...)
  :prompt-transforms (FUNCTIONS...)

See `gptel-make-preset' for a description of options.

NOTE: This is dangerous to use — except in the case where you only ever
have one single backend-provider that offers a common on normalizing
API, such as exclusively using LiteLLM.

As an example of the danger, if you set `:request-params' via a preset
and then later change to another preset that moves to a different
backend without changing those request parameters, or if the users
directly changes the backend, then the `:request-params' set by the
preset could become invalid, since different backends interpret them
differently or may not accept what another backend consider legitimate."
  (declare (indent 1))
  (let ((params (plist-get keys :request-params))
        (transforms (plist-get keys :prompt-transforms)))
    (when (or params transforms)
      (plist-put
       keys :post
       `(lambda ()
          ,(if params
               `(setq-local gptel--request-params
                            (gptel--merge-plists gptel--request-params
                                                 ,params)))
          ,@(if transforms
                (mapcar #'(lambda (transform)
                            `(add-hook 'gptel-prompt-transform-functions
                                       #',transform nil 'local))
                        (eval transforms)))))
      (if params (cl-remf keys :request-params))
      (if transforms (cl-remf keys :prompt-transforms)))
    `(gptel-make-preset ,name ,@keys)))

;;; MODELS ===============================================================

;;; OpenAI

(gptel-make-preset 'gpt
  :description "OpenAI's ChatGPT"
  ;; :backend "ChatGPT"
  ;; :model 'gpt-4.1
  :backend "LiteLLM"
  :model 'openai/gpt-4.1-2025-04-14
  :temperature 1.0)

;;; Anthropic

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

;;; Ali Baba

(gptel-make-preset 'qwen
  :description "Ali Baba's Qwen, thinking"
  ;; :backend "llama-swap-hera"
  ;; :model 'Qwen3-235B-A22B
  :backend "LiteLLM"
  ;; :model 'hera/Qwen3-235B-A22B-Instruct-2507
  :model 'hera/Qwen3-Coder-480B-A35B-Instruct-1M
  :temperature 1.0)

;;; DeepSeek

(gptel-make-preset 'r1
  :description "DeepSeek R1"
  ;; :backend "llama-swap-hera"
  ;; :model 'DeepSeek-R1-0528
  :backend "LiteLLM"
  ;; :model 'hera/DeepSeek-R1-0528
  :model 'openrouter/deepseek/deepseek-r1-0528:free
  :temperature 0.6)

(gptel-make-preset 'fast
  :description "DeepSeek R1, quick"
  ;; :backend "llama-swap-hera"
  ;; :model 'DeepSeek-R1-0528-Qwen3-8B
  :backend "LiteLLM"
  :model 'hera/DeepSeek-R1-0528-Qwen3-8B
  :temperature 0.6)

;;; Perplexity

(my/gptel-make-preset 'sonar
  :description "Perplexity.ai sonar-pro"
  :backend "LiteLLM"
  :model 'perplexity/sonar-pro
  :include-reasoning 'ignore)

(my/gptel-make-preset 'pro
  :description "Perplexity.ai sonar-reasoning-pro"
  :backend "LiteLLM"
  :model 'perplexity/sonar-reasoning-pro
  :include-reasoning 'ignore)

(my/gptel-make-preset 'deep-research
  :description "Perplexity.ai sonar-deep-research"
  :backend "LiteLLM"
  :model 'perplexity/sonar-deep-research
  :include-reasoning 'ignore)

;;; ALIASES ==============================================================

(gptel-make-preset 'default
  :description "Default setup"
  :parents 'qwen
  :system 'default
  :confirm-tool-calls 'auto
  :max-tokens 8192
  :use-context 'user
  :include-reasoning 'ignore)

(my/gptel-make-preset 'code
  :description "Best model for generating or interpreting code"
  :parents 'opus
  :request-params '(:thinking
                    (:type "enabled" :budget_tokens 16384)
                    :max_tokens 24000)
  :include-reasoning 'ignore)

(gptel-make-preset 'rewrite
  :description "Model used for basic rewrites"
  :max-tokens 8192
  :include-reasoning nil
  :tools nil
  :parents `(quick
             ,(if gptel-presets-rewrite-use-remote
                  'gpt
                'qwen)))

;;; DIRECTIVES (w/ MODELS) ===============================================

;;; Refinement

(gptel-make-preset 'prompt
  :description "AI prompt refiner"
  :system 'prompt
  :parents 'gpt
  :tools nil
  :max-tokens nil
  :include-reasoning 'ignore)

(gptel-make-preset 'title
  :description "Create Org-mode title"
  :system 'title
  :parents 'rewrite)

;;; Languages

(gptel-make-preset 'persian
  :description "Persian translator"
  :system 'persian
  :parents 'gpt
  :max-tokens 2048)

(gptel-make-preset 'spanish
  :description "Spanish translator"
  :system 'spanish
  :parents 'gpt
  :max-tokens 2048)

;;; Computing

(gptel-make-preset 'cli
  :description "Generate command-line commands"
  :system 'cli
  :parents 'opus)

(gptel-make-preset 'emacs
  :description "Best model for generating or interpreting code"
  :system 'emacs-aid
  :parents 'qwen
  :max-tokens 32767
  :tools '("emacs"))

(gptel-make-preset 'haskell
  :description "Expert Haskell coder"
  :system 'haskell
  :parents 'opus
  :max-tokens 1024)

;;; REQUEST-PARAMS =======================================================

(my/gptel-make-preset 'here
  :description "Add user location to query"
  :request-params `(:user_location
                    (:latitude
                     ,calendar-latitude
                     :longitude
                     ,calendar-longitude
                     :country "US")))

(my/gptel-make-preset 'web
  :description "Search the Web using Perplexity.ai"
  :parents 'sonar
  :request-params '(:web_search_options (:search_context_size "medium"))
  :include-reasoning 'ignore)

(my/gptel-make-preset 'deep
  :description "Search the Web (deeply) using Perplexity.ai"
  :parents 'sonar
  :request-params '(:web_search_options (:search_context_size "high"))
  :include-reasoning 'ignore)

(my/gptel-make-preset 'think
  :description "Search the Web (deeply) using Perplexity.ai"
  :parents 'pro
  :request-params '(:web_search_options (:search_context_size "high"))
  :include-reasoning 'ignore)

(my/gptel-make-preset 'research
  :description "Perplexity.ai deep reasoning"
  :parents 'deep-research
  :request-params '(:web_search_options (:search_context_size "high"))
  :include-reasoning 'ignore)

;;; PROMPT-TRANSFORMS ====================================================

(my/gptel-make-preset 'quick
  :prompt-transforms '(gptel-presets-insert-no-think))

(my/gptel-make-preset 'rag
  :rag-config-file "~/src/rag-client/chat.yaml"
  :rag-files-and-directories '("~/dl/world.txt")
  :rag-top-k 3
  :prompt-transforms '(gptel-rag-transform))

;;; REWRITES =============================================================

(gptel-make-preset 'shorten
  :description "Shorten Org-mode titles"
  :rewrite-directive 'shorten
  :rewrite-message "Shorten it as described."
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
