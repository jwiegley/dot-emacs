;;; gptel-ext --- Extra functions for use with gptel -*- lexical-binding: t -*-

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
(eval-when-compile
  (require 'cl))

(require 'solar)
(require 'gptel)

(defconst gptel-ext-rewrite-use-remote t
  "Non-nil if we should use remote models (local is unavailable?).")

(defsubst gptel-ext-insert-no-think ()
  "Insert the text /no_think at the end of the user prompt."
  (insert " /no_think"))

(gptel-make-preset 'gpt
  :description "OpenAI's ChatGPT"
  :backend "ChatGPT"
  :model 'gpt-4.1
  :temperature 1.0)

(gptel-make-preset 'sonnet
  :description "Anthropic's Claude Sonnet, thinking"
  :backend "Claude-thinking"
  :model 'claude-sonnet-4-20250514
  :temperature 1.0)

(gptel-make-preset 'opus
  :description "Anthropic's Claude Opus, thinking"
  :backend "Claude-thinking"
  :model 'claude-opus-4-20250514
  :temperature 1.0)

(gptel-make-preset 'code
  :description "Best model for generating or interpreting code"
  :parents 'opus)

(gptel-make-preset 'qwen
  :description "Ali Baba's Qwen, thinking"
  :backend "llama-swap-hera"
  :model 'Qwen3-235B-A22B
  :temperature 1.0)

(gptel-make-preset 'r1
  :description "DeepSeek R1"
  :backend "llama-swap-hera"
  :model 'DeepSeek-R1-0528
  :temperature 0.6)

(gptel-make-preset 'r1q
  :description "DeepSeek R1, quick"
  :backend "llama-swap-hera"
  :model 'DeepSeek-R1-0528-Qwen3-8B
  :temperature 0.6)

(gptel-make-preset 'web
  :description "Perplexity.ai sonar-pro"
  :backend "Perplexity"
  :model 'sonar-pro
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

(gptel-make-preset 'think
  :description "Perplexity.ai sonar-reasoning-pro"
  :backend "Perplexity"
  :model 'sonar-reasoning-pro
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

(gptel-make-preset 'deep
  :description "Perplexity.ai deep reasoning"
  :backend "Perplexity"
  :model 'sonar-deep-research
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
                      #'gptel-ext-insert-no-think nil 'local)))

(gptel-make-preset 'rewrite
  :description "Model used for basic rewrites"
  :max-tokens 8192
  :include-reasoning nil
  :tools nil
  :parents `(quick
             ,(if gptel-ext-rewrite-use-remote
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

(defun gptel-ext-shorten ()
  "Given a selected set of Org-mode headings, shorten them."
  (interactive)
  (gptel-with-preset 'shorten (gptel--suffix-rewrite)))

(defun gptel-ext-title ()
  "Given a region of text, generate a title to describe it."
  (interactive)
  (gptel-with-preset 'title
    (gptel-request
        (if (region-active-p)
            (buffer-substring-no-properties
             (region-beginning) (region-end))
          (buffer-string))
      :transforms gptel-prompt-transform-functions
      :callback (lambda (resp info)
                  (when (stringp resp)
                    (with-current-buffer (plist-get info :buffer)
                      (goto-char (plist-get info :position))
                      (org-back-to-heading)
                      (goto-char (line-end-position))
                      (unless (looking-back " ")
                        (insert " "))
                      (insert resp)))))))

(gptel-make-tool
 :function (lambda (location unit)
             (url-retrieve-synchronously "api.weather.com/..."
                                         location unit))
 :name "get_weather"
 :description "Get the current weather in a given location"
 :args
 (list
  '(:name "location"
          :type string
          :description "The city and state, e.g. San Francisco, CA")
  '(:name "unit"
          :type string
          :enum ["celsius" "farenheit"]
          :description
          "The unit of temperature, either 'celsius' or 'fahrenheit'"
          :optional t)))

(defun gptel-ext-code-infill ()
  "Fill in code at point based on buffer context.  Note: Sends the whole buffer."
  (let ((lang (gptel--strip-mode-suffix major-mode)))
    `(,(format "You are a %s programmer and assistant in a code buffer in a text editor.

Follow my instructions and generate %s code to be inserted at the cursor.
For context, I will provide you with the code BEFORE and AFTER the cursor.


Generate %s code and only code without any explanations or markdown code fences.  NO markdown.
You may include code comments.

Do not repeat any of the BEFORE or AFTER code." lang lang lang)
      nil
      "What is the code AFTER the cursor?"
      ,(format "AFTER\n```\n%s\n```\n"
               (buffer-substring-no-properties
                (if (use-region-p) (max (point) (region-end)) (point))
                (point-max)))
      "And what is the code BEFORE the cursor?"
      ,(format "BEFORE\n```%s\n%s\n```\n" lang
               (buffer-substring-no-properties
                (point-min)
                (if (use-region-p) (min (point) (region-beginning)) (point))))
      ,(if (use-region-p) "What should I insert at the cursor?"))))

(defun gptel-ext-clear-buffer ()
  "Create a new chat session in the current GPTel buffer."
  (interactive)
  (if nil
      (progn
        (erase-buffer)
        (insert "*Prompt*: "))
    (org-shifttab 0)
    (goto-char (point-max))
    (org-insert-heading)
    (insert "New chat\n\n*Prompt*: ")))

(defun gptel-ext-write-to-org-roam ()
  "If a chat buffer is saved with \\[save-buffer], create an Org-roam file."
  (remove-hook 'write-contents-functions
               #'gptel-ext-write-to-org-roam)
  (set-visited-file-name
   (expand-file-name (format-time-string "%Y%m%d%H%M-chat.org")
                     "~/org/agent"))
  (save-excursion
    (goto-char (point-min))
    (run-hooks 'org-capture-before-finalize-hook)
    (vulpea-buffer-prop-set "title" "Chat")
    (org-roam-ext-sort-file-properties)))

(defun gptel-ext-write-to-org-roam-install ()
  "Use `gptel-ext-write-to-org-roam' if a GPTel buffer is saved."
  (add-hook 'gptel-mode-hook
            #'(lambda ()
                (unless (buffer-file-name)
                  (add-hook 'write-contents-functions
                            #'gptel-ext-write-to-org-roam)))))

(defun synchronous-bugged (func)
  "Make any asynchronous function into a synchronous one.
FUNC is called with a callback to be called when the asynchronous
function is finished. For example, in the case where `make-thread' is
used to run a function asynchronously, which when complete, finishes the
synchronous call.

  (synchronous
     #'(lambda (k)
         (make-thread #'(lambda ()
                          (sleep-for 3)
                          (funcall k 123)))))"
  (let* ((mut (make-mutex))
         (var (make-condition-variable mut))
         (result (cons nil nil)))
    (funcall func
             #'(lambda (x)
                 (with-mutex mut
                   (setf (car result) t)
                   (setf (cdr result) x)
                   (condition-notify var))))
    (with-mutex mut
      (while (null (car result))
        (sleep-for 0 1)
        (condition-wait var)))
    (cdr result)))

(defun synchronous (func)
  "Run the given asynchronous function FUNC synchronously."
  (let ((result (cons nil nil)))
    (funcall func
             #'(lambda (res)
                 (setf (cdr result) res)
                 (setf (car result) t)))
    (while (null (car result))
      (accept-process-output nil 0.1))
    (cdr result)))

(cl-defun gptel-request-synchronous
    (&optional prompt &key callback
               (buffer (current-buffer))
               position context dry-run
               (stream nil) (in-place nil)
               (system gptel--system-message)
               transforms (fsm (gptel-make-fsm)))
  "Synchronous version of `gptel-request'."
  (synchronous
   #'(lambda (komplete)
       (gptel-request
           prompt
         :callback
         #'(lambda (response info)
             (if callback
                 (funcall callback response info))
             (if (stringp response)
                 (funcall komplete response)))
         :buffer buffer
         :position position
         :context context
         :dry-run dry-run
         :stream stream
         :in-place in-place
         :system system
         :transforms transforms
         :fsm fsm))))

(defun llm (prompt)
  "Invoke the current LLM with a PROMPT, returning the response.
For example:
  (llm \"What is your name? /no_think\")"
  (with-temp-buffer
    (gptel-request-synchronous
     prompt
     :callback `(lambda (response _info)
                  (when (stringp response)
                    (with-current-buffer ,(current-buffer)
                      (insert response)))))
    (buffer-string)))

(defun gptel-ext-multi-send ()
  "Send a GPTel query to multiple models at once."
  (interactive)
  (let ((gptel-prompt-prefix-alist nil)
        (gptel-response-prefix-alist nil)
        (gptel-response-separator "")
        (gptel-stream nil))
    (let ((gptel-backend (gptel-get-backend "Claude"))
          (gptel-model 'claude-3-7-sonnet-20250219))
      (insert (propertize "** Response (Claude):\n" 'gptel 'ignore))
      (gptel-send))
    (insert "\n\n" (propertize "** Response (Gemini):\n" 'gptel 'ignore))
    (let ((gptel-backend (gptel-get-backend "Gemini"))
          (gptel-model 'gemini-2.0-flash))
      (gptel-send))
    (insert "\n\n" (propertize "** Response (ChatGPT):\n" 'gptel 'ignore))
    (let ((gptel-backend (gptel-get-backend "ChatGPT"))
          (gptel-model 'gpt-4o-mini))
      (gptel-send))))

(provide 'gptel-ext)

;;; gptel-ext.el ends here
