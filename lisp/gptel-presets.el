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
(require 'gptel-anthropic)
(require 'hf)

(defsubst gptel-presets-insert-no-think ()
  "Insert the text /no_think at the end of the user prompt."
  (insert " /no_think"))

;;; MODELS ===============================================================

;;; OpenAI

(gptel-make-preset 'gpt
  :description "OpenAI's ChatGPT"
  :backend "LiteLLM"
  :model 'openai/gpt-4.1
  :temperature 1.0)

(gptel-make-preset 'gpt-oss
  :description "OpenAI's ChatGPT, Open Source"
  :backend "LiteLLM"
  :model 'hera/gpt-oss-120b
  :temperature 1.0)

(gptel-make-preset 'gpt-oss-travel
  :description "OpenAI's ChatGPT, Open Source (small)"
  :backend "llama-swap"
  :model 'gpt-oss-20b
  :temperature 1.0)

(gptel-make-preset 'minimax-m2
  :description "MiniMax-M2"
  :backend "LiteLLM"
  :model 'hera/MiniMax-M2
  :temperature 1.0
  :prompt-transform-functions
  `(:append
    (list
     ,(lambda (fsm)   ;Remove non-delimited <think>...</think> block for minimax-m2
        (let* ((info (gptel-fsm-info fsm))
               (callback
                (or (plist-get info :callback) 'gptel--insert-response)))
          (plist-put info :callback
                     (lambda (resp info)
                       (when (stringp resp)
                         ;; Remove everything up to and including </think>
                         (when-let* ((idx (string-search "</think>" resp)))
                           ;; 8 = length of "</think>"
                           (setq resp (substring resp (+ idx 8)))))
                       (funcall callback resp info))))))))

;;; Anthropic

(gptel-make-anthropic "Claude"          ;Any name you want
  :stream t                             ;Streaming responses
  :key gptel-api-key)

(defvar claude-opus-model 'claude-opus-4-5-20251101)
(defvar claude-sonnet-model 'claude-sonnet-4-5-20250929)
(defvar claude-haiku-model 'claude-haiku-4-5-20251001)

(gptel-make-preset 'opus
  :description "Anthropic's Claude Opus, thinking"
  :backend "LiteLLM"
  :model (intern (format "anthropic/%s" claude-opus-model))
  :temperature 1.0)

(gptel-make-preset 'sonnet
  :description "Anthropic's Claude Sonnet, thinking"
  :backend "LiteLLM"
  :model (intern (format "anthropic/%s" claude-sonnet-model))
  :temperature 1.0)

(gptel-make-preset 'haiku
  :description "Anthropic's Claude Haiku"
  :backend "LiteLLM"
  :model (intern (format "anthropic/%s" claude-haiku-model))
  :temperature 1.0)

(gptel-make-preset 'opus-max
  :description "Anthropic's Claude Opus, thinking"
  :backend "Claude-Anthropic"
  :model claude-opus-model
  :temperature 1.0)

(gptel-make-preset 'sonnet-max
  :description "Anthropic's Claude Sonnet, thinking"
  :backend "Claude-Anthropic"
  :model claude-sonnet-model
  :temperature 1.0)

(gptel-make-preset 'haiku-max
  :description "Anthropic's Claude Haiku"
  :backend "Claude-Anthropic"
  :model claude-haiku-model
  :temperature 1.0)

(gptel-make-preset 'opus-direct
  :description "Anthropic's Claude Opus"
  :backend "Claude"
  :model claude-opus-model
  :temperature 1.0)

(gptel-make-preset 'sonnet-direct
  :description "Anthropic's Claude Sonnet"
  :backend "Claude"
  :model claude-sonnet-model
  :temperature 1.0)

(gptel-make-preset 'haiku-direct
  :description "Anthropic's Claude Haiku"
  :backend "Claude"
  :model claude-haiku-model
  :temperature 1.0)

;;; Perplexity

(gptel-make-preset 'sonar
  :description "Perplexity.ai sonar-pro"
  :backend "LiteLLM"
  :model 'perplexity/sonar-pro)

(gptel-make-preset 'sonar-pro
  :description "Perplexity.ai sonar-reasoning-pro"
  :backend "LiteLLM"
  :model 'perplexity/sonar-reasoning-pro)

(gptel-make-preset 'sonar-deep-research
  :description "Perplexity.ai sonar-deep-research"
  :backend "LiteLLM"
  :model 'perplexity/sonar-deep-research)

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

(gptel-make-preset 'high-output
  :request-params '(:merge (:max_tokens 32000)))

(gptel-make-preset 'low-thinking
  :request-params '(:merge (:thinking (:type "enabled" :budget_tokens 8000))))

(gptel-make-preset 'medium-thinking
  :request-params '(:merge (:thinking (:type "enabled" :budget_tokens 16000))))

(gptel-make-preset 'high-thinking
  :request-params '(:merge (:thinking (:type "enabled" :budget_tokens 32000))))

(gptel-make-preset 'web-search
  :request-params '(:merge (:tools [(:type "web_search_20250305"
                                           :name "web_search"
                                           :max_uses 5)])))

(gptel-make-preset 'default
  :description "Default setup"
  :parents 'opus-max
  :system 'default
  :confirm-tool-calls nil               ; 'auto
  :use-context 'user
  :pre (lambda () (gptel-mcp-connect
              '(;; "memory-keeper"
                ;; "Ref"
                ;; "context7"
                ;; "fetch"
                ;; "github"
                "perplexity"
                "sequential-thinking"
                ;; "time"
                )
              'sync))
  :tools '(:append (;; "mcp-memory-keeper"
                    ;; "mcp-Ref"
                    ;; "mcp-context7"
                    ;; "mcp-fetch"
                    ;; "mcp-github"
                    "mcp-perplexity"
                    "mcp-sequential-thinking"
                    ;; "mcp-time"
                    ))
  :system '(:append "

- Use sequential-thinking MCP when appropriate to break down tasks further.
- Use context7 MCP and Ref MCP whenever code examples might help.
- Use memory-keeper MCP to record and recall conversations."))

(gptel-make-preset 'analyze
  :description "Best model for analysis"
  :parents '(opus-max high-thinking high-output))

(gptel-make-preset 'code
  :description "Best model for generating or interpreting code"
  :parents 'analyze)

(gptel-make-preset 'search
  :description "Best model for web search and analysis"
  :parents '(analyze web-search))

(gptel-make-preset 'rewrite
  :description "Model used for basic rewrites"
  :include-reasoning nil
  :use-context nil
  :tools nil
  :parents (or
            'gpt-oss-travel
            'sonnet
            'opus-max
            'gpt-oss
            'haiku
            'haiku-max
            'haiku-direct
            'gpt
            ))

(gptel-make-preset 'visible-buffers
  :description "Include the full text of all buffers visible in the frame."
  :context
  '(:eval (mapcar #'window-buffer
                  (delq (selected-window) (window-list)))))

(gptel-make-preset 'visible-text
  :description "Include visible text from all windows in the frame."
  :context
  '(:eval
    (letrec ((contexts
              (mapcar
               (lambda (win)
                 (list (window-buffer win)
                       (make-overlay (window-start win) (window-end win)
                                     (window-buffer win))))
               (delq (selected-window) (window-list))))
             (cleanup
              (lambda ()
                (remove-hook 'gptel-post-request-hook cleanup)
                (cl-loop for (buf . ovs) in contexts
                         do (mapc #'delete-overlay ovs)))))
      (add-hook 'gptel-post-request-hook cleanup)
      contexts)))

;;; DIRECTIVES (w/ MODELS) ===============================================

;;; Refinement

(gptel-make-preset 'prompt
  :description "AI prompt refiner"
  :system 'prompt
  :parents 'opus)

(gptel-make-preset 'title
  :description "Create Org-mode title"
  :system 'title
  :parents 'rewrite)

;;; Languages

(gptel-make-preset 'persian
  :description "Persian translator"
  :system 'persian
  :parents 'sonnet)

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
  :system 'emacs
  :parents 'sonnet
  :tools '("emacs" "introspection"))

(gptel-make-preset 'haskell
  :description "Expert Haskell coder"
  :system 'haskell
  :parents 'sonnet)

;;; REQUEST-PARAMS =======================================================

;; (gptel-make-preset 'here
;;   :description "Add user location to query"
;;   :request-params '(:merge (:user_location
;;                              (:latitude
;;                               ,calendar-latitude
;;                               :longitude
;;                               ,calendar-longitude
;;                               :country "US"))))

(gptel-make-preset 'web
  :description "Search the Web using Perplexity.ai"
  ;; :parents '(here sonar)
  :parents 'sonar
  :request-params '(:merge (:web_search_options (:search_context_size "medium"))))

(gptel-make-preset 'deep
  :description "Search the Web (deeply) using Perplexity.ai"
  ;; :parents '(here sonar)
  :parents 'sonar
  :request-params '(:merge (:web_search_options (:search_context_size "high"))))

(gptel-make-preset 'think
  :description "Search the Web (deeply) using Perplexity.ai"
  ;; :parents '(here sonar-pro)
  :parents 'sonar-pro
  :request-params '(:merge (:web_search_options (:search_context_size "high"))))

(gptel-make-preset 'research
  :description "Perplexity.ai deep reasoning"
  ;; :parents '(here sonar-deep-research)
  :parents 'sonar-deep-research
  :request-params '(:merge (:web_search_options (:search_context_size "high"))))

;;; PROMPT-TRANSFORMS ====================================================

(gptel-make-preset 'rag
  :rag-config-file "~/src/rag-client/chat.yaml"
  :rag-files-and-directories '("~/dl/world.txt")
  :rag-top-k 3
  :prompt-transform-functions '(:append (gptel-rag-transform)))

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

(gptel-make-preset 'breakdown
  :description "Break down complex Org-mode task into smaller subtasks"
  :rewrite-directive 'breakdown
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
          " code within progn blocks. Do not enclose the rewritten code in"
          " Markdown code block markers.")
  :parents '(emacs rewrite))

(provide 'gptel-presets)

;;; gptel-presets.el ends here
