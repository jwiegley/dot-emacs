;;; ghub.el --- minuscule client for the Github API  -*- lexical-binding: t -*-

;; Copyright (C) 2016-2017  Jonas Bernoulli

;; Author: Jonas Bernoulli <jonas@bernoul.li>
;; Homepage: https://github.com/magit/ghub
;; Keywords: tools
;; Package-Requires: ((emacs "24.4"))

;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a copy of the GPL see https://www.gnu.org/licenses/gpl.txt.

;;; Commentary:

;; A minuscule client for the Github API.

;; This library just provides the HTTP methods.
;; See https://developer.github.com/v3 for valid requests.

;; Initial configuration
;; ---------------------
;;
;;   $ git config --global github.user <username>
;;   $ emacs ~/.authinfo.gpg
;;   # -*- epa-file-encrypt-to: ("A.U.Thor@example.com") -*-
;;   machine api.github.com login <login> password <token>
;;
;; To acquire a token, go to https://github.com/settings/tokens.  Note
;; that currently the same token is shared by all Emacs packages that
;; use `ghub.el'.

;; Usage examples
;; --------------
;;
;; Getting details about a repository:
;;
;;   (ghub-get "/repos/tarsius/ghub")
;;
;; Listing names of all repositories of a user:
;;
;;   (--keep (cdr (assq 'name it))
;;           (let ((ghub-unpaginate t))
;;             (ghub-get "/users/tarsius/repos")))
;;
;; Making an unauthenticated request:
;;
;;   (let ((ghub-authenticate nil))
;;     (ghub-get "/orgs/magit/repos"))
;;
;; Making a request using basic authentication:
;;
;;   (let ((ghub-authenticate 'basic))
;;     (ghub-get "/orgs/magit/repos"))

;; Github Enterprise support
;; -------------------------
;;
;; Initial configuration:
;;
;;   $ git config --global github.gh.example.com.user employee
;;   $ emacs ~/.authinfo.gpg
;;   # -*- epa-file-encrypt-to: ("employee@example.com") -*-
;;   machine gh.example.com login employee password <token>
;;
;; Making a request:
;;
;;   (let ((ghub-base-url "https://gh.example.com"))
;;     (ghub-get "/users/employee/repos"))

;;; Code:

(require 'auth-source)
(require 'cl-lib)
(require 'json)
(require 'url)
(require 'url-auth)

(eval-when-compile (require 'subr-x))

(defvar url-http-end-of-headers)
(defvar url-http-response-status)

;;; Request
;;;; API

(defvar ghub-base-url "https://api.github.com")
(defvar ghub-authenticate t)
(defvar ghub-token nil)
(defvar ghub-username nil)
(defvar ghub-unpaginate nil)
(defvar ghub-extra-headers nil)
(defvar ghub-read-response-function 'ghub--read-json-response)

(defvar ghub-response-headers nil)

(defun ghub-get (resource &optional params data noerror)
  "Make `GET' request for RESOURCE, optionally sending PARAMS and/or DATA.
Signal an error if the status code isn't in the 2xx class;
unless optional NOERROR is non-nil, in which case return nil."
  (ghub-request "GET" resource params data noerror))

(defun ghub-put (resource &optional params data noerror)
  "Make `PUT' request for RESOURCE, optionally sending PARAMS and/or DATA.
Signal an error if the status code isn't in the 2xx class;
unless optional NOERROR is non-nil, in which case return nil."
  (ghub-request "PUT" resource params data noerror))

(defun ghub-head (resource &optional params data noerror)
  "Make `HEAD' request for RESOURCE, optionally sending PARAMS and/or DATA.
Signal an error if the status code isn't in the 2xx class;
unless optional NOERROR is non-nil, in which case return nil."
  (ghub-request "HEAD" resource params data noerror))

(defun ghub-post (resource &optional params data noerror)
  "Make `POST' request for RESOURCE, optionally sending PARAMS and/or DATA.
Signal an error if the status code isn't in the 2xx class;
unless optional NOERROR is non-nil, in which case return nil."
  (ghub-request "POST" resource params data noerror))

(defun ghub-patch (resource &optional params data noerror)
  "Make `PATCH' request for RESOURCE, optionally sending PARAMS and/or DATA.
Signal an error if the status code isn't in the 2xx class;
unless optional NOERROR is non-nil, in which case return nil."
  (ghub-request "PATCH" resource params data noerror))

(defun ghub-delete (resource &optional params data noerror)
  "Make `DELETE' request for RESOURCE, optionally sending PARAMS and/or DATA.
Signal an error if the status code isn't in the 2xx class; unless
optional NOERROR is non-nil, in which case return nil."
  (ghub-request "DELETE" resource params data noerror))

(define-error 'ghub-error "Ghub Error")
(define-error 'ghub-http-error "HTTP Error" 'ghub-error)
(define-error 'ghub-301 "Moved Permanently" 'ghub-http-error)
(define-error 'ghub-400 "Bad Request" 'ghub-http-error)
(define-error 'ghub-401 "Unauthorized" 'ghub-http-error)
(define-error 'ghub-403 "Forbidden" 'ghub-http-error)
(define-error 'ghub-404 "Not Found" 'ghub-http-error)
(define-error 'ghub-422 "Unprocessable Entity" 'ghub-http-error)

(defun ghub-request (method resource &optional params data noerror)
  "Make a request using METHOD for RESOURCE.
METHOD is a `HTTP' request method, a string.  If non-nil, send
PARAMS and/or DATA in the request.  Signal an error if the status
code isn't in the 2xx class; unless optional NOERROR is non-nil,
in which case return nil."
  (let* ((p (and params (concat "?" (ghub--url-encode-params params))))
         (d (and data   (encode-coding-string (json-encode-list data) 'utf-8)))
         (buf (let ((url-request-extra-headers
                     `(("Content-Type"  . "application/json")
                       ,@(and ghub-authenticate
                              (list (cons "Authorization"
                                          (ghub--auth ghub-authenticate))))
                       ,@ghub-extra-headers))
                    (url-request-method method)
                    (url-request-data d))
                (url-retrieve-synchronously (concat ghub-base-url resource p)))))
    (unwind-protect
        (with-current-buffer buf
          (set-buffer-multibyte t)
          (let (link body)
            (goto-char (point-min))
            (let (headers)
              (while (re-search-forward "^\\([^:]*\\): \\(.+\\)"
                                        url-http-end-of-headers t)
                (push (cons (match-string 1)
                            (match-string 2))
                      headers))
              (and (setq link (cdr (assoc "Link" headers)))
                   (setq link (car (rassoc
                                    (list "rel=\"next\"")
                                    (mapcar (lambda (elt) (split-string elt "; "))
                                            (split-string link ",")))))
                   (string-match "[?&]page=\\([^&>]+\\)" link)
                   (setq link (match-string 1 link)))
              (setq ghub-response-headers (nreverse headers)))
            (unless url-http-end-of-headers
              (error "ghub: url-http-end-of-headers is nil when it shouldn't"))
            (goto-char (1+ url-http-end-of-headers))
            (setq body (funcall ghub-read-response-function))
            (unless (or noerror (= (/ url-http-response-status 100) 2))
              (let ((data (list method resource p d body)))
                (pcase url-http-response-status
                  (301 (signal 'ghub-301 data))
                  (400 (signal 'ghub-400 data))
                  (401 (signal 'ghub-401 data))
                  (403 (signal 'ghub-403 data))
                  (404 (signal 'ghub-404 data))
                  (422 (signal 'ghub-422 data))
                  (_   (signal 'ghub-http-error
                               (cons url-http-response-status data))))))
            (if (and link ghub-unpaginate)
                (nconc body
                       (ghub-request method resource
                                     (cons (cons 'page link)
                                           (cl-delete 'page params :key #'car))
                                     data noerror))
              body)))
      (kill-buffer buf))))

(define-obsolete-function-alias 'ghub--request 'ghub-request "Ghub 2.0")

(defun ghub-wait (resource)
  "Busy-wait until RESOURCE becomes available."
  (with-local-quit
    (let ((for 0.5)
          (total 0))
      (while (not (ignore-errors (ghub-get resource)))
        (setq for (truncate (* 2 for)))
        (setq total (+ total for))
        (when (= for 128)
          (signal 'ghub-error
                  (list (format "Github is taking too long to create %s"
                                resource))))
        (message "Waiting for %s (%ss)..." resource total)
        (sit-for for)))))

;;;; Internal

(defun ghub--read-json-response ()
  (and (not (eobp))
       (let ((json-object-type 'alist)
             (json-array-type  'list)
             (json-key-type    'symbol)
             (json-false       nil)
             (json-null        nil))
         (json-read-from-string (ghub--read-raw-response)))))

(defun ghub--read-raw-response ()
  (and (not (eobp))
       (decode-coding-string
        (buffer-substring-no-properties (point) (point-max))
        'utf-8)))

(defun ghub--url-encode-params (params)
  (mapconcat (lambda (param)
               (concat (url-hexify-string (symbol-name (car param))) "="
                       (url-hexify-string (cdr param))))
             params "&"))

;;; Authentication
;;;; Internal

(defun ghub--auth (auth)
  (encode-coding-string
   (if (eq auth 'basic)
       (ghub--basic-auth)
     (concat "token "
             (if (stringp auth) auth (ghub--token))))
   'utf-8))

(defun ghub--basic-auth ()
  (let ((url (url-generic-parse-url ghub-base-url)))
    (setf (url-user url)
          (ghub--username))
    (url-basic-auth url t)))

(defun ghub--token ()
  "Return the configured token.
Use `auth-source-search' to get the token for the user returned
by `ghub--username' and a host based on `ghub-base-url'.  When
`ghub-token' is non-nil, then return its value instead."
  (or ghub-token
      (ghub--auth-source-get :secret
        :host (ghub--hostname)
        :user (ghub--username))
      (signal 'ghub-error '("Token not found"))))

(defun ghub--hostname ()
  (save-match-data
    (if (string-match "\\`https?://\\([^/]+\\)" ghub-base-url)
        (match-string 1 ghub-base-url)
      (signal 'ghub-error '("Invalid value for ghub-base-url")))))

(defun ghub--username ()
  "Return the configured username.
For Github.com get the value of the Git variable `github.user'.
For Github enterprise instances, get the value of the Git
variable `github.HOST.user'."
  (or ghub-username
      (let ((var (if (string-equal ghub-base-url "https://api.github.com")
                     "github.user"
                   (format "github.%s.user" (ghub--hostname)))))
        (condition-case nil
            (car (process-lines "git" "config" var))
          (error
           (signal 'ghub-error (list (format "%s is undefined" var))))))))

(defun ghub--auth-source-get (key:s &rest spec)
  (declare (indent 1))
  (let ((plist (car (apply #'auth-source-search :max 1 spec))))
    (cl-flet ((value (k) (let ((v (plist-get plist k)))
                           (if (functionp v) (funcall v) v))))
      (if (listp key:s)
          (mapcar #'value key:s)
        (value key:s)))))

;;; ghub.el ends soon
(provide 'ghub)
;; Local Variables:
;; indent-tabs-mode: nil
;; End:
;;; ghub.el ends here
