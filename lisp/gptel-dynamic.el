;;; gptel-dynamic --- Dynamic Contexts for GPTel

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
;; A "dynamic context" is context that is added to a query based on
;; information determined at the time of submission. This information can come
;; from anywhere, and must simply result in text to be appended to the either
;; the system or user context of the query.

(require 'cl-lib)
(require 'cl-macs)
(eval-when-compile
  (require 'cl))

(require 'gptel)

(defcustom gptel-dynamic-pre-augment-hook nil
  "Hook run before dynamically extending the context of a gptel request.

This runs before any request is submitted."
  :type 'hook)

(defcustom gptel-dynamic-post-augment-hook nil
  "Hook run after dynamically extending the context of a gptel request.

This runs (possibly) before any request is submitted."
  :type 'hook)

(defun gptel-dynamic--handle-augment (fsm)
  "Augment the request contained in state machine FSM's info."
  (let* ((info (gptel-fsm-info fsm))
         (data (plist-get info :data))
         (messages (plist-get data :messages)))
    (message "messages = %s" messages))
  (run-hooks 'gptel-dynamic-pre-extend-hook)
  (gptel--fsm-transition fsm)
  (run-hooks 'gptel-dynamic-post-extend-hook)
  (with-current-buffer (plist-get (gptel-fsm-info fsm) :buffer)
    (gptel--update-status " Augmenting..." 'warning)))

(defun gptel-dynamic-install ()
  (setq gptel-request--transitions
        `((INIT . ((t                       . AUGMENT)))
          (AUGMENT . ((t                       . WAIT)))
          (WAIT . ((t                       . TYPE)))
          (TYPE . ((,#'gptel--error-p       . ERRS)
                   (,#'gptel--tool-use-p    . TOOL)
                   (t                       . DONE)))
          (TOOL . ((,#'gptel--error-p       . ERRS)
                   (,#'gptel--tool-result-p . WAIT)
                   (t                       . DONE))))
        gptel-request--handlers
        `((AUGMENT ,#'gptel-dynamic--handle-augment)
          (WAIT ,#'gptel--handle-wait)
          (TOOL ,#'gptel--handle-tool-use))
        gptel-send--handlers
        `((AUGMENT ,#'gptel-dynamic--handle-augment)
          (WAIT ,#'gptel--handle-wait)
          (TYPE ,#'gptel--handle-pre-insert)
          (ERRS ,#'gptel--handle-error ,#'gptel--fsm-last)
          (TOOL ,#'gptel--handle-tool-use)
          (DONE ,#'gptel--handle-post-insert ,#'gptel--fsm-last))))

(provide 'gptel-dynamic)
