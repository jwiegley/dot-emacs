;;; gptel-rag --- Augment Contexts for GPTel

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

(defun gptel-rag-to-file (entry)
  "Convert ENTRY to a file pathname.
This argument is accepted in one of two forms:

1. It is a singleton list of the form (filename)
2. It is a cons cell of the form (buffer . (overlay1 overlay2 ...))"
  (car entry))

(defvar gptel-rag-content-limit 1 ;; 32768
  "Maximum size in bytes that can be used for file content.")

(defvar gptel-rag-top-k 10)

(defvar gptel-rag-client-exe "~/src/rag-client/result/bin/rag-client")

(defvar gptel-rag-embed-model "BAAI/bge-large-en-v1.5")

(defvar gptel-rag-cache-dir "~/.cache/rag-client")

(defun gptel-rag--collection-size (collection)
  (if (listp collection)
      (apply #'+ (mapcar #'(lambda (entry)
                             (file-attribute-size (file-attributes entry)))
                         collection))
    0))

(defun gptel-rag--collection-hash (collection)
  (with-temp-buffer
    (dolist (entry collection)
      (insert (with-temp-buffer
                (insert-file-contents-literally entry)
                (secure-hash 'sha512 (current-buffer))))
      (insert ?\n))
    (secure-hash 'sha512 (current-buffer))))

(defun gptel-rag--call-rag-client (collection query)
  (with-temp-buffer
    (dolist (entry collection)
      (insert (expand-file-name entry) ?\n))
    (call-process-region
     (point-min) (point-max)
     gptel-rag-client-exe
     t t nil
     "--embed-model" gptel-rag-embed-model
     "--cache-dir" (expand-file-name
                    (gptel-rag--collection-hash collection)
                    gptel-rag-cache-dir)
     "--top-k" (number-to-string gptel-rag-top-k)
     "--query" query)
    (goto-char (point-min))
    (mapcar #'(lambda (result)
                (cons (alist-get 'file_name (alist-get 'metadata result))
                      (alist-get 'text result)))
            (json-read))))

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
                     `((:role "system" :content ,message))))
  (message "data is now: %s" (pp-to-string data)))

(defsubst gptel-rag-add-system-message (info message)
  "Add MESSAGE to the set of query messages."
  (gptel-rag--append-system-message (plist-get info :data) message))

(defun gptel-rag (info)
  (let ((paths (mapcar #'gptel-rag-to-file
                       (plist-get (plist-get info :data) :collection))))
    (when (> (gptel-rag--collection-size paths) gptel-rag-content-limit)
      (plist-put (plist-get info :data) :collection nil)
      (message "Indexing and querying document collection...")
      (let ((nodes (gptel-rag--call-rag-client
                    paths (gptel-rag-last-user-message info))))
        (message "nodes = %s" nodes)
        (dolist (node nodes)
          (gptel-rag-add-system-message
           info
           (with-temp-buffer
             (insert "In file `" (car node) "` (citation):\n\n```"
                     (cdr node)
                     "\n```\n")
             (buffer-string)))))
      info)))

(defun gptel-rag-install ()
  (add-hook 'gptel-rag-handler-functions #'gptel-rag))

(provide 'gptel-rag)
