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
(require 'hf)

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
  (let* ((keys (cl-copy-list keys))
         (params (plist-get keys :request-params))
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
  :backend "LiteLLM"
  :model 'openai/gpt-4.1
  :temperature 1.0)

;;; Anthropic

(gptel-make-preset 'haiku
  :description "Anthropic's Claude Haiku"
  :backend "LiteLLM"
  :model 'anthropic/claude-3-5-haiku-20241022
  :max-tokens 8192
  :temperature 1.0)

(gptel-make-preset 'haiku-max
  :description "Anthropic's Claude Haiku"
  :backend "Claude-OAuth"
  :model 'claude-3-5-haiku-20241022
  :max-tokens 8192
  :temperature 0.4)

(gptel-make-preset 'sonnet
  :description "Anthropic's Claude Sonnet, thinking"
  :backend "LiteLLM"
  :model 'anthropic/claude-sonnet-4-20250514
  :temperature 1.0)

(gptel-make-preset 'sonnet-max
  :description "Anthropic's Claude Sonnet, thinking"
  :backend "Claude-OAuth"
  :model 'claude-sonnet-4-20250514
  :temperature 1.0)

(gptel-make-preset 'opus
  :description "Anthropic's Claude Opus, thinking"
  :backend "LiteLLM"
  :model 'anthropic/claude-opus-4-1-20250805
  :temperature 1.0)

(gptel-make-preset 'opus-max
  :description "Anthropic's Claude Opus, thinking"
  :backend "Claude-OAuth"
  :model 'claude-opus-4-1-20250805
  :temperature 1.0)

;;; Perplexity

(my/gptel-make-preset 'sonar
  :description "Perplexity.ai sonar-pro"
  :backend "LiteLLM"
  :model 'perplexity/sonar-pro
  :include-reasoning 'ignore)

(my/gptel-make-preset 'sonar-pro
  :description "Perplexity.ai sonar-reasoning-pro"
  :backend "LiteLLM"
  :model 'perplexity/sonar-reasoning-pro
  :include-reasoning 'ignore)

(my/gptel-make-preset 'sonar-deep-research
  :description "Perplexity.ai sonar-deep-research"
  :backend "LiteLLM"
  :model 'perplexity/sonar-deep-research
  :include-reasoning 'ignore)

;;; Ali Baba

(gptel-make-preset 'qwen
  :description "Ali Baba's Qwen, thinking"
  :backend "LiteLLM"
  :model 'hera/Qwen3-235B-A22B-Thinking-2507
  :temperature 1.0)

;;; DeepSeek

(gptel-make-preset 'r1
  :description "DeepSeek R1"
  :backend "LiteLLM"
  :model 'hera/DeepSeek-R1-0528
  :temperature 0.6)

(gptel-make-preset 'r1-fast
  :description "DeepSeek R1, quick"
  :backend "LiteLLM"
  :model 'hera/DeepSeek-R1-0528-Qwen3-8B
  :temperature 0.6)

(gptel-make-preset 'deepseek
  :description "DeepSeek V3.1"
  :backend "LiteLLM"
  :model 'hera/DeepSeek-V3.1
  :temperature 0.6)

;;; Other

(gptel-make-preset 'kimi
  :description "Kimi K2"
  :backend "LiteLLM"
  :model 'hera/Kimi-K2-Instruct
  :temperature 0.6)

;;; ALIASES ==============================================================

(gptel-make-preset 'default
  :description "Default setup"
  :parents 'opus-max
  ;; :model hf-default-instance-name
  :system 'default
  :confirm-tool-calls nil ; 'auto
  :use-context 'user
  :include-reasoning 'ignore)

(my/gptel-make-preset 'code
  :description "Best model for generating or interpreting code"
  :parents 'opus-max
  :request-params '(:thinking
                    (:type "enabled" :budget_tokens 24000)
                    :max_tokens 32000)
  :include-reasoning 'ignore)

(my/gptel-make-preset 'analyze
  :description "Best model for analysis"
  :parents 'opus-max
  :request-params '(:thinking
                    (:type "enabled" :budget_tokens 24000)
                    :max_tokens 32000)
  :include-reasoning 'ignore)

(my/gptel-make-preset 'search
  :description "Best model for web search and analysis"
  :parents 'opus-max
  :request-params '(:thinking
                    (:type "enabled" :budget_tokens 24000)
                    :max_tokens 32000
                    :tools [(:type "web_search_20250305"
                                   :name "web_search"
                                   :max_uses 5)])
  :include-reasoning 'ignore)

(gptel-make-preset 'rewrite
  :description "Model used for basic rewrites"
  :include-reasoning nil
  :tools nil
  :parents (if gptel-presets-rewrite-use-remote
               (or 'gpt 'haiku)
             'qwen))

;;; DIRECTIVES (w/ MODELS) ===============================================

;;; Refinement

(gptel-make-preset 'prompt
  :description "AI prompt refiner"
  :system 'prompt
  :parents 'sonnet
  :tools nil
  :include-reasoning 'ignore)

(gptel-make-preset 'title
  :description "Create Org-mode title"
  :system 'title
  :parents 'rewrite)

;;; Languages

(gptel-make-preset 'persian
  :description "Persian translator"
  :system 'persian
  :parents 'opus)

(gptel-make-preset 'spanish
  :description "Spanish translator"
  :system 'spanish
  :parents 'sonnet)

;;; Computing

(gptel-make-preset 'cli
  :description "Generate command-line commands"
  :system 'cli
  :parents 'sonnet)

(gptel-make-preset 'emacs
  :description "Best model for generating or interpreting code"
  :system 'emacs-aid
  :parents 'opus
  :tools '("emacs" "introspection"))

(gptel-make-preset 'haskell
  :description "Expert Haskell coder"
  :system 'haskell
  :parents 'opus)

;;; REQUEST-PARAMS =======================================================

;; (my/gptel-make-preset 'here
;;   :description "Add user location to query"
;;   :request-params `(:user_location
;;                     (:latitude
;;                      ,calendar-latitude
;;                      :longitude
;;                      ,calendar-longitude
;;                      :country "US")))

(my/gptel-make-preset 'web
  :description "Search the Web using Perplexity.ai"
  ;; :parents '(here sonar)
  :parents 'sonar
  :request-params '(:web_search_options (:search_context_size "medium"))
  :include-reasoning 'ignore)

(my/gptel-make-preset 'deep
  :description "Search the Web (deeply) using Perplexity.ai"
  ;; :parents '(here sonar)
  :parents 'sonar
  :request-params '(:web_search_options (:search_context_size "high"))
  :include-reasoning 'ignore)

(my/gptel-make-preset 'think
  :description "Search the Web (deeply) using Perplexity.ai"
  ;; :parents '(here sonar-pro)
  :parents 'sonar-pro
  :request-params '(:web_search_options (:search_context_size "high"))
  :include-reasoning 'ignore)

(my/gptel-make-preset 'research
  :description "Perplexity.ai deep reasoning"
  ;; :parents '(here sonar-deep-research)
  :parents 'sonar-deep-research
  :request-params '(:web_search_options (:search_context_size "high"))
  :include-reasoning 'ignore)

;;; PROMPT-TRANSFORMS ====================================================

(my/gptel-make-preset 'rag
  :rag-config-file "~/src/rag-client/chat.yaml"
  :rag-files-and-directories '("~/dl/world.txt")
  :rag-top-k 3
  :prompt-transforms '(gptel-rag-transform))

(gptel-make-preset 'cache
  :pre
  (lambda ()
    (save-excursion
      (while (re-search-backward "\b@cache\b" nil t)
        (delete-region (match-beginning 0) (match-end 0)))))
  :cache t)

(gptel-make-preset 'json
  :pre (lambda ()
         (setq-local gptel--schema
                     (buffer-substring-no-properties
                      (point) (point-max)))
         (delete-region (point) (point-max))))

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
