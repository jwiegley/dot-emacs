;;; magithub-proxy.el --- Fake repository context  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: tools

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Jump to issues from `magit-status'!

;;; Code:

(require 'magit)

(defmacro magithub-with-proxy (remote &rest body)
  "Using REMOTE as `origin', run BODY."
  (declare (indent 1))
  `(magithub--proxy-with-remote ,remote (lambda () ,@body)))

(defconst magithub--proxy-remote-url-config
  '("remote" "origin" "url")
  "The config path to origin's URL.")

(defun magithub--proxy-current-remote ()
  "The current remote of `origin'."
  (apply #'magit-get magithub--proxy-remote-url-config))

(defun magithub--proxy-set-remote (remote)
  "Set the remote of `origin'."
  (apply #'magit-set remote magithub--proxy-remote-url-config))

(defun magithub--proxy-with-remote (remote f)
  "Using REMOTE as `origin', execute function F.
F should take no arguments."
  (if remote
      (let ((real-origin-remote (magithub--proxy-current-remote)))
        (prog2 (magithub--proxy-set-remote remote)
            (condition-case err
                (funcall f)
              ;; if F throws errors, make sure to restore the real remote
              (error (magithub--proxy-set-remote real-origin-remote)
                     (error err)))
          (magithub--proxy-set-remote real-origin-remote)))
    (funcall f)))

(defun magithub-proxy-default-proxy ()
  "Get the default proxy for this repository."
  (magit-get "magithub" "proxy"))

(defun magithub-proxy-set-default (remote)
  "Set REMOTE as the proxy for this repository."
  (interactive (list (ignore-errors
                       (magit-read-url
                        "Please enter the remote url to use for Magithub functionality"
                        (or (magithub-proxy-default-proxy)
                            (magit-get "remote" (magit-get "branch" "master" "remote") "url")
                            (magithub--proxy-current-remote))))))
  (if (or (string= remote "")
          (string= remote (magithub--proxy-current-remote)))
      (magit-set nil "magithub" "proxy")
    (magit-set remote "magithub" "proxy"))
  (magithub-issue-refresh))

(provide 'magithub-proxy)
;;; magithub-proxy.el ends here
