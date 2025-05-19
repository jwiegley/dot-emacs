;;; gptel-rag --- Augment Contexts for GPTel     -*- lexical-binding: t; -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 28 Apr 2025
;; Version: 0.1
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
;;
;; A "augment context" is context that is added to a query based on
;; information determined at the time of submission. This information can come
;; from anywhere, and must simply result in text to be appended to the either
;; the system or user context of the query.

(require 'cl-lib)
(require 'cl-macs)
(eval-when-compile
  (require 'cl))

(require 'gptel)

(defcustom gptel-rag-client-exe "rag-client"
  "Name or path of the rag-client executable."
  :type 'file)

(defcustom gptel-rag-embed-provider "HuggingFace"
  "Provider to use for text embeddings.
TODO: In future, allow models from different providers, such as OpenAI."
  :type 'string)

(defcustom gptel-rag-embed-model "BAAI/bge-large-en-v1.5"
  "Model to use for text embeddings.
TODO: In future, allow models from different providers, such as OpenAI."
  :type 'string)

(defcustom gptel-rag-content-limit 32768
  "Maximum size in bytes that can be used for file content."
  :type 'integer)

(defcustom gptel-rag-embed-dim 1024
  "Vector dimensions used by `gptel-rag-embed-model'. Must match!"
  :type 'integer)

(defcustom gptel-rag-chunk-size 512
  "Size of textual chunks when splitting documents."
  :type 'integer)

(defcustom gptel-rag-chunk-overlap 16
  "Amount of overlap between chunks when splitting documents."
  :type 'integer)

(defcustom gptel-rag-top-k 10
  "Return the top K document nodes when querying a collection."
  :type 'integer)

(defun gptel-rag-to-file (entry)
  "Convert ENTRY to a file pathname.
This argument is accepted in one of two forms:

1. It is a singleton list of the form (filename)
2. It is a cons cell of the form (buffer . (overlay1 overlay2 ...))"
  (car entry))

(defun gptel-rag--collection-size (collection)
  (if (listp collection)
      (apply #'+ (mapcar #'(lambda (entry)
                             (file-attribute-size (file-attributes entry)))
                         collection))
    0))

(defun gptel-rag--call-rag-client (callback fsm collection query)
  (with-temp-buffer
    (dolist (entry collection)
      (insert (expand-file-name entry) ?\n))
    (message "Indexing and querying document collection...")
    (let ((proc
           (make-process
            :name "*rag-client*"
            :buffer "*rag-client-output*"
            :command
            (list (executable-find gptel-rag-client-exe)
                  "--embed-model" gptel-rag-embed-model
                  "--embed-dim" gptel-rag-embed-dim
                  "--chunk-size" gptel-rag-chunk-size
                  "--chunk-overlap" gptel-rag-chunk-overlap
                  "--top-k" (number-to-string gptel-rag-top-k)
                  "--from" "-"
                  "search" query)
            :connection-type 'pipe
            :sentinel
            #'(lambda (proc event)
                (unless (process-live-p proc)
                  (with-current-buffer (process-buffer proc)
                    (goto-char (point-min))
                    (funcall
                     callback
                     (mapcar
                      #'(lambda (result)
                          (cons (alist-get 'file_name
                                           (alist-get 'metadata result))
                                (alist-get 'text result)))
                      (json-read)))))))))
      (process-send-string proc (buffer-string))
      (process-send-eof proc)
      (setf (alist-get proc gptel--request-alist)
            (cons fsm
                  #'(lambda ()
                      (set-process-sentinel proc #'ignore)
                      (delete-process proc)
                      (sleep-for 0 100)
                      (kill-buffer (process-buffer proc))))))))

(defun gptel-rag--get-user-messages (messages)
  "Return a list of strings representing all user messages in INFO."
  (cl-loop for msg in messages
           if (string= (plist-get msg :role) "user")
           collect (plist-get msg :content)))

(defun gptel-rag-last-user-message (info)
  "Return the last user message found in a set of query messages."
  (car
   (last
    (gptel-rag--get-user-messages
     (plist-get (plist-get info :data) :full-prompt)))))

(defun gptel-rag--append-system-message (data message)
  "Format a string message as a system message.
The exact representation may different depending on the backend."
  (plist-put data :full-prompt
             (append (plist-get data :full-prompt)
                     `((:role "system" :content ,message)))))

(defsubst gptel-rag-add-system-message (info message)
  "Add MESSAGE to the set of query messages."
  (gptel-rag--append-system-message (plist-get info :data) message))

(defun gptel-rag (callback fsm)
  (let* ((info (gptel-fsm-info fsm))
         (paths (mapcar #'gptel-rag-to-file
                        (plist-get (plist-get info :data) :collection))))
    ;; jww (2025-05-16): Instead of passing a :collection keyword in the info
    ;; plist, I could just call `gptel-context--collect' here.
    (if (> (gptel-rag--collection-size paths) gptel-rag-content-limit)
        (progn
          (plist-put (plist-get info :data) :collection nil)
          (gptel-rag--call-rag-client
           #'(lambda (nodes)
               (dolist (node nodes)
                 (gptel-rag-add-system-message
                  info
                  (with-temp-buffer
                    (insert "In file `" (car node) "` (citation):\n\n```"
                            (cdr node)
                            "\n```\n")
                    (buffer-string))))
               (funcall callback info))
           fsm paths (gptel-rag-last-user-message info)))
      (funcall callback fsm))))

(defun gptel-rag-install ()
  (add-hook 'gptel-rag-handler-functions #'gptel-rag))

(provide 'gptel-rag)
