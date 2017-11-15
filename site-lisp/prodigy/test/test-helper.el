;;; test-helper.el --- Prodigy: Test helpers -*- lexical-binding: t; -*-

;; Copyright (C) 2014 Johan Andersson

;; Author: Johan Andersson <johan.rejeep@gmail.com>
;; Maintainer: Johan Andersson <johan.rejeep@gmail.com>

;; This file is NOT part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; Code:

(require 'f)
(require 'json)

(defvar prodigy-test/test-path
  (f-parent (f-this-file)))

(defvar prodigy-test/root-path
  (f-parent prodigy-test/test-path))

(defun plist-keys (plist)
  "Return a list containing all the keys in PLIST."
  (when plist
    (cons
     (car plist)
     (plist-keys
      (cddr plist)))))

(defvar prodigy-test/port 1333
  "The test server will run on this port.")

(defun prodigy-test/make-service (&rest args)
  "Create a test service.

If ARGS are specified, they will override the default."
  (let ((server-path (f-expand "server.coffee" prodigy-test/test-path)))
    (let* ((port prodigy-test/port)
           (service
            (list :name "Test Service"
                  :command "coffee"
                  :args (list server-path)
                  :port port
                  :env `(("PORT" ,(number-to-string port))))))
      (mapc
       (lambda (property)
         (plist-put service property (plist-get args property)))
       (plist-keys args))
      (car (apply 'prodigy-define-service service)))))

(defun prodigy-test/post-message (service action &rest args)
  "Post a message to the SERVICE process.

ACTION and ARGS are json encoded and sent to the process."
  (let ((process
         (make-network-process
          :name "Test Server Connector"
          :host "127.0.0.1"
          :service (plist-get service :port))))
    (process-send-string process (json-encode (cons action args)))))

(defun prodigy-test/log-lines (service n)
  "Log N lines into the process ouptut."
  (--dotimes n
    (prodigy-test/post-message service 'log
                               (concat "Line " (number-to-string it)))))

(defmacro with-sandbox (&rest body)
  "Yield BODY in a sandboxed environment."
  `(with-temp-buffer
     (setq prodigy-tags nil)
     (setq prodigy-services nil)
     (setq prodigy-status-list nil)
     (setq prodigy-start-tryouts 1)
     (setq prodigy-stop-tryouts 1)
     (setq prodigy-filters nil)
     (setq prodigy-view-truncate-by-default nil)
     (with-mock ,@body)))

(defun prodigy-test/delay (seconds callback)
  "Wait SECONDS, then run function CALLBACK."
  (declare (indent 1))
  (run-at-time seconds nil callback))

(require 'prodigy (f-expand "prodigy" prodigy-test/root-path))
(require 'ert)
(require 'ert-async)
(require 'el-mock)
(eval-when-compile
  (require 'cl))

(provide 'prodigy-test-helper)

;;; test-helper.el ends here
