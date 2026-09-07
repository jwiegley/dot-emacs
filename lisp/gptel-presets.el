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
(require 'gptel-openai)
(require 'gptel-anthropic)
(require 'llm-setup)

;;; MODELS ===============================================================

;;; OpenAI

(gptel-make-openai "ChatGPT"
  :stream t
  :key gptel-api-key)

(gptel-make-preset 'gpt
  :description "OpenAI's ChatGPT"
  :backend "ChatGPT"
  :model (llm-setup-policy-model "emacs" "presets" "gpt")
  :temperature (llm-setup-policy "emacs" "temperature"))

;;; Anthropic

(gptel-make-anthropic "Claude"          ;Any name you want
  :stream t                             ;Streaming responses
  :key gptel-api-key)

(defvar claude-opus-model (llm-setup-policy-model "emacs" "presets" "opus"))
(defvar claude-sonnet-model (llm-setup-policy-model "emacs" "presets" "sonnet"))
(defvar claude-haiku-model (llm-setup-policy-model "emacs" "presets" "haiku"))

(gptel-make-preset 'opus
  :description "Anthropic's Claude Opus, thinking"
  :backend "Claude"
  :model claude-opus-model
  :temperature (llm-setup-policy "emacs" "temperature"))

(gptel-make-preset 'sonnet
  :description "Anthropic's Claude Sonnet, thinking"
  :backend "Claude"
  :model claude-sonnet-model
  :temperature (llm-setup-policy "emacs" "temperature"))

(gptel-make-preset 'haiku
  :description "Anthropic's Claude Haiku"
  :backend "Claude"
  :model claude-haiku-model
  :temperature (llm-setup-policy "emacs" "temperature"))

(gptel-make-preset 'opus-max
  :description "Anthropic's Claude Opus, thinking"
  :backend "vibe-proxy"
  :model (llm-setup-policy-model "emacs" "presets" "opus-max")
  :temperature (llm-setup-policy "emacs" "temperature"))

(gptel-make-preset 'sonnet-max
  :description "Anthropic's Claude Sonnet, thinking"
  :backend "vibe-proxy"
  :model (llm-setup-policy-model "emacs" "presets" "sonnet-max")
  :temperature (llm-setup-policy "emacs" "temperature"))

;;; Perplexity

(gptel-make-preset 'sonar
  :description "Perplexity search"
  :backend "Perplexity"
  :model (llm-setup-policy-model "emacs" "presets" "sonar"))

(gptel-make-preset 'sonar-pro
  :description "Perplexity reasoning search"
  :backend "Perplexity"
  :model (llm-setup-policy-model "emacs" "presets" "sonar-pro"))

(gptel-make-preset 'sonar-deep-research
  :description "Perplexity deep research"
  :backend "Perplexity"
  :model (llm-setup-policy-model "emacs" "presets" "sonar-deep-research"))

;;; Ali Baba

(gptel-make-preset 'qwen
  :description "Default local model"
  :backend "oMLX"
  :model (llm-setup-default-model-name))

(gptel-make-preset 'qwen-clio
  :description "Compatibility alias for the shared local default"
  :parents (llm-setup-policy-symbols "emacs" "parents" "qwen-clio"))

;;; ALIASES ==============================================================

(gptel-make-preset 'high-output
  :request-params `(:merge (:max_tokens ,(llm-setup-policy "emacs" "highOutputTokens"))))

(gptel-make-preset 'web-search
  :request-params '(:merge (:tools [(:type "web_search_20250305"
                                           :name "web_search"
                                           :max_uses 5)])))

(gptel-make-preset 'default
  :description "Default setup"
  ;; :parents 'opus-max
  :parents (llm-setup-policy-symbols "emacs" "parents" "default")
  :system 'default
  :confirm-tool-calls nil               ; 'auto
  :use-context 'user
  ;; :pre (lambda () (gptel-mcp-connect
  ;;             '(;; "memory-keeper"
  ;;               ;; "Ref"
  ;;               ;; "context7"
  ;;               ;; "fetch"
  ;;               ;; "github"
  ;;               ;; "perplexity"
  ;;               ;; "sequential-thinking"
  ;;               ;; "time"
  ;;               )
  ;;             'sync))
  ;; :tools '(:append (;; "mcp-memory-keeper"
  ;;                   ;; "mcp-Ref"
  ;;                   ;; "mcp-context7"
  ;;                   ;; "mcp-fetch"
  ;;                   ;; "mcp-github"
  ;;                   ;; "mcp-perplexity"
  ;;                   ;; "mcp-sequential-thinking"
  ;;                   ;; "mcp-time"
  ;;                   ))
  ;;   :system '(:append "

  ;; - Use sequential-thinking MCP when appropriate to break down tasks further.
  ;; - Use Perplexy MCP to research subjects further on the Internet.")
  )

(gptel-make-preset 'analyze
  :description "Best model for analysis"
  :parents (llm-setup-policy-symbols "emacs" "parents" "analyze"))

(gptel-make-preset 'code
  :description "Best model for generating or interpreting code"
  :parents (llm-setup-policy-symbols "emacs" "parents" "code"))

(gptel-make-preset 'search
  :description "Best model for web search and analysis"
  :parents (llm-setup-policy-symbols "emacs" "parents" "search"))

(gptel-make-preset 'rewrite
  :description "Model used for basic rewrites"
  :include-reasoning nil
  :use-context nil
  :tools nil
  :parents (llm-setup-policy-symbols "emacs" "parents" "rewrite"))

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
  :parents (llm-setup-policy-symbols "emacs" "parents" "prompt"))

(gptel-make-preset 'title
  :description "Create Org-mode title"
  :system 'title
  :parents (llm-setup-policy-symbols "emacs" "parents" "title"))

(gptel-make-preset 'infer-tasks
  :description "Infer Org-mode tasks from text"
  :system 'infer-tasks
  :parents (llm-setup-policy-symbols "emacs" "parents" "infer-tasks"))

;;; Languages

(gptel-make-preset 'persian
  :description "Persian translator"
  :system 'persian
  :parents (llm-setup-policy-symbols "emacs" "parents" "persian"))

(gptel-make-preset 'spanish
  :description "Spanish translator"
  :system 'spanish
  :parents (llm-setup-policy-symbols "emacs" "parents" "spanish"))

;;; Computing

(gptel-make-preset 'cli
  :description "Generate command-line commands"
  :system 'cli
  :parents (llm-setup-policy-symbols "emacs" "parents" "cli"))

(gptel-make-preset 'emacs
  :description "Best model for generating or interpreting code"
  :system 'emacs
  :parents (llm-setup-policy-symbols "emacs" "parents" "emacs")
  :tools '("emacs" "introspection"))

(gptel-make-preset 'haskell
  :description "Expert Haskell coder"
  :system 'haskell
  :parents (llm-setup-policy-symbols "emacs" "parents" "haskell"))

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
  :parents (llm-setup-policy-symbols "emacs" "parents" "web")
  :request-params '(:merge (:web_search_options
                            (:search_context_size "medium"))))

(gptel-make-preset 'deep
  :description "Search the Web (deeply) using Perplexity.ai"
  ;; :parents '(here sonar)
  :parents (llm-setup-policy-symbols "emacs" "parents" "deep")
  :request-params '(:merge (:web_search_options
                            (:search_context_size "high"))))

(gptel-make-preset 'research
  :description "Perplexity.ai deep reasoning"
  ;; :parents '(here sonar-deep-research)
  :parents (llm-setup-policy-symbols "emacs" "parents" "research")
  :request-params '(:merge (:web_search_options
                            (:search_context_size "high"))))

(gptel-make-preset 'think
  :description "Enable reasoning/thinking"
  :request-params '(:merge (:chat_template_kwargs
                            (:enable_thinking
                             t
                             :preserve_thinking
                             t))))

(gptel-make-preset 'nothink
  :description "Disable reasoning/thinking"
  :request-params '(:merge (:chat_template_kwargs
                            (:enable_thinking
                             :json-false
                             :preserve_thinking
                             :json-false))))

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
  :parents (llm-setup-policy-symbols "emacs" "parents" "shorten"))

(gptel-make-preset 'breakdown
  :description "Break down complex Org-mode task into smaller subtasks"
  :system 'breakdown
  :parents (llm-setup-policy-symbols "emacs" "parents" "breakdown"))

(gptel-make-preset 'proof
  :description "Proofread and spell-checking"
  :rewrite-directive 'proofread
  :rewrite-message "Proofread as instructed."
  :parents (llm-setup-policy-symbols "emacs" "parents" "proof"))

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
  :parents (llm-setup-policy-symbols "emacs" "parents" "docstring"))

(provide 'gptel-presets)

;;; gptel-presets.el ends here
