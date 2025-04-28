;;; gptel-augment --- Augment Contexts for GPTel

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

(defcustom gptel-augment-pre-modify-hook nil
  "Hook run before augmentally extending the context of a gptel request.

This runs before any request is submitted."
  :type 'hook)

(defcustom gptel-augment-post-modify-hook nil
  "Hook run after augmentally extending the context of a gptel request.

This runs (possibly) before any request is submitted."
  :type 'hook)

(defcustom gptel-augment-info-functions
  (list
   #'(lambda (info)
       (message "Being asked to augment last user message: %s"
                (gptel-augment-last-user-message info))
       info)
   #'my-gptel-augment-with-current-temperature
   #'(lambda (info)
       (ignore (message "Messages are now: %s" (pp-to-string info)))))
  "List of handlers used to augment a query before sending it.

Note that while this can certainly be set with a global value to
be applied to all queries in all buffers, it meant to be set
locally for a specific buffer, or chat topic, or only the context
of using a certain agent."
  :type 'hook)

(defun gptel-augment--handle-augment (fsm)
  "Augment the request contained in state machine FSM's info."
  (let* ((info (gptel-fsm-info fsm)))
    (cl-loop for fn in gptel-augment-info-functions
             for result = info then (or (funcall fn result) result)
             finally (return result)))
  (run-hooks 'gptel-augment-pre-modify-hook)
  (gptel--fsm-transition fsm)
  (run-hooks 'gptel-augment-post-modify-hook)
  (with-current-buffer (plist-get (gptel-fsm-info fsm) :buffer)
    (gptel--update-status " Augmenting..." 'warning)))

(cl-defgeneric gptel-augment--get-user-messages (_backend messages)
  "Return a list of strings representing all user messages in INFO."
  (cl-loop for msg across messages
           if (string= (plist-get msg :role) "user")
           collect (plist-get msg :content)))

(defun gptel-augment-last-user-message (info)
  "Return the last user message found in a set of query messages."
  (car
   (last
    (gptel-augment--get-user-messages
     (plist-get info :backend)
     (plist-get (plist-get info :data) :messages)))))

(cl-defgeneric gptel-augment--append-system-message (_backend data message)
  "Format a string message as a system message.
The exact representation may different depending on the backend."
  (gptel--inject-prompt _backend data
                        (gptel-augment--create-system-message _backend message)))

(defun gptel-augment-add-system-message (info message)
  "Add MESSAGE to the set of query messages."
  (gptel-augment--append-system-message
   (plist-get info :backend)
   (plist-get info :data)
   message))

(defun gptel-augment-install ()
  (setq gptel-request--transitions
        `((INIT    . ((t                       . AUGMENT)))
          (AUGMENT . ((t                       . WAIT)))
          (WAIT    . ((t                       . TYPE)))
          (TYPE    . ((,#'gptel--error-p       . ERRS)
                      (,#'gptel--tool-use-p    . TOOL)
                      (t                       . DONE)))
          (TOOL    . ((,#'gptel--error-p       . ERRS)
                      (,#'gptel--tool-result-p . WAIT)
                      (t                       . DONE))))
        gptel-request--handlers
        `((AUGMENT ,#'gptel-augment--handle-augment)
          (WAIT    ,#'gptel--handle-wait)
          (TOOL    ,#'gptel--handle-tool-use))
        gptel-send--handlers
        `((AUGMENT ,#'gptel-augment--handle-augment)
          (WAIT    ,#'gptel--handle-wait)
          (TYPE    ,#'gptel--handle-pre-insert)
          (ERRS    ,#'gptel--handle-error ,#'gptel--fsm-last)
          (TOOL    ,#'gptel--handle-tool-use)
          (DONE    ,#'gptel--handle-post-insert ,#'gptel--fsm-last))))

(defun my-current-temperature (place)
  (interactive "sLocation: ")
  (with-current-buffer
      (url-retrieve-synchronously
       (url-encode-url
        (format
         "http://api.weatherapi.com/v1/current.json?key=%s&q=%s&aqi=yes"
         (lookup-password "api.weatherapi.com" "jwiegley@gmail.com" 80)
         place)))
    (goto-char (point-min))
    (goto-char url-http-end-of-headers)
    (let ((json (json-parse-buffer :object-type 'alist)))
      (kill-buffer (current-buffer))
      (alist-get 'temp_f (alist-get 'current json)))))

(defun my-gptel-augment-with-current-temperature (messages)
  (let ((last-user (gptel-augment-last-user-message messages)))
    (when (string-match "temperature in \\(.+?\\)\\?" last-user)
      (gptel-augment-add-system-message
       messages
       (let ((place (match-string 1 last-user)))
         (format "The current temperature in %s is %s"
                 place (my-current-temperature place)))))))

(provide 'gptel-augment)
