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
(require 'solar)
(require 'gptel)
(require 'org-ext)

(defun gptel-ext-with-region (preset beg end body-fn)
  "Send region BEG to END to gptel and process response with BODY-FN.
PRESET is a gptel preset symbol or configuration to use for the request.
BODY-FN is a callback function receiving the response string, called
with point at the original request position within the entry buffer."
  (gptel-with-preset preset
    (gptel-request (buffer-substring-no-properties beg end)
      :callback (lambda (resp info)
                  (when (stringp resp)
                    (with-current-buffer (plist-get info :buffer)
                      (goto-char (plist-get info :position))
                      (goto-char end)
                      (funcall body-fn resp)))))))

(defun gptel-ext-with-org-entry (preset body-fn)
  "Send narrowed Org entry to gptel and process response with BODY-FN.
PRESET is a gptel preset symbol or configuration to use for the request.
BODY-FN is a callback function receiving the response string, called
with point at the original request position within the entry buffer."
  (org-ext-with-entry-narrowed
   (gptel-ext-with-region preset (point-min) (point-max) body-fn)))

(defun gptel-ext-shorten ()
  "Given a selected set of Org-mode headings, shorten them."
  (interactive)
  (gptel-with-preset 'shorten (gptel--suffix-rewrite)))

(defun gptel-ext-breakdown ()
  "Given an Org-mode task, break it down into other tasks."
  (interactive)
  (gptel-ext-with-org-entry
   'breakdown
   (lambda (resp)
     (unless (bolp) (insert ?\n))
     (insert resp)
     (unless (bolp) (insert ?\n)))))

(defun gptel-ext-proofread ()
  "Given selected text, proofread it."
  (interactive)
  (gptel-with-preset 'proof (gptel--suffix-rewrite)))

(defun gptel-ext-docstring ()
  "Given selected text, proofread it."
  (interactive)
  (gptel-with-preset 'docstring (gptel--suffix-rewrite)))

(defun gptel-ext-title ()
  "Generate and insert an AI-generated title for the current Org entry.
Uses `gptel-ext-with-org-entry' to request a title suggestion, then
inserts the response at the end of the current heading line."
  (interactive)
  (gptel-ext-with-org-entry
   'title
   (lambda (resp)
     (forward-line -1)
     (org-back-to-heading)
     (goto-char (line-end-position))
     (unless (looking-back " " (line-beginning-position))
       (insert " "))
     (insert resp))))

(defun gptel-ext-infer-tasks (beg end)
  "Send region to gptel using the infer-tasks preset and insert response.

BEG and END define the region boundaries to send as the prompt.
The response is inserted at point in the original buffer."
  (interactive "r")
  (gptel-ext-with-region 'infer-tasks beg end #'insert))

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
     #\\='(lambda (k)
         (make-thread #\\='(lambda ()
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
        (sleep-for 0)
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
  "Make a synchronous GPT request and block until response is received.

This function wraps `gptel-request' to provide synchronous behavior,
blocking execution until the API response is complete. Returns the
response string from the language model.

PROMPT is the text input to send to the language model. If nil, uses the
current buffer contents or context.

Optional keyword arguments:

CALLBACK   - Function called with (RESPONSE INFO) after completion.
             Receives the model's response string and metadata plist.

BUFFER     - Buffer to use for the request context. Defaults to current
             buffer.

POSITION   - Position in buffer to insert response when :in-place is non-nil.

CONTEXT    - Additional context to include with the request.

DRY-RUN    - If non-nil, prepare request but don't actually send it.

STREAM     - If non-nil, enable streaming responses (not typically useful
             for synchronous requests).

IN-PLACE   - If non-nil, insert response directly into buffer at position.

SYSTEM     - System message/instructions for the model. Defaults to
             `gptel--system-message'.

TRANSFORMS - List of transformation functions to apply to response.

FSM        - Finite state machine for managing request state. Defaults
             to new FSM from `gptel-make-fsm'.

Returns the response string from the language model.

Example:
  (let ((response (gptel-request-synchronous \"Explain Emacs\")))
    (message \"Got: %s\" response))"
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

(defun gptel-ext-commit-summary ()
  "Insert a commit message header line in the format I use.
This is followed by a standard magit (GNU style) changelog.

Don't get the LLM to write the commit message itself, because it's bad
at inferring my intent.

Intended to be placed in `git-commit-setup-hook'."
  (unless (string-match-p "/org/" default-directory)
    (gptel-with-preset 'commit-summary
      (let ((commit-buffer (current-buffer))) ;commit message buffer

        (with-temp-buffer
          (vc-git-command              ;insert diff
           (current-buffer) 1 nil
           "diff-index"
           "--unified=16"
           "--patch"
           "--minimal"
           "--ignore-all-space"
           "--exit-code"
           (and (magit-anything-staged-p) "--cached")
           "HEAD" "--")

          (gptel-request nil           ;Run request on diff buffer contents
            :context commit-buffer
            :callback
            (lambda (resp info)
              (if (not (stringp resp))
                  (message "Git commit summary generation failed")
                (with-current-buffer (plist-get info :context)
                  (save-excursion
                    (goto-char (point-min))
                    (insert resp "\n\n")
                    (magit-generate-changelog)))))))))))

(defun gptel-ext-commit-summary-install ()
  "Install `gptel-ext-commit-summary' into `git-commit-setup-hook'.

Registers the commit summary function to run during git commit setup
and configures the commit-summary preset for gptel with rewrite-style
system prompt."
  (add-hook 'git-commit-setup-hook #'gptel-ext-commit-summary 50)

  (with-eval-after-load 'gptel
    (gptel-make-preset 'commit-summary
      :system 'commit-summary
      :parents 'rewrite)))

(provide 'gptel-ext)

;;; gptel-ext.el ends here
