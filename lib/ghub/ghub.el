;;; ghub.el --- minuscule client library for the Github API  -*- lexical-binding: t -*-

;; Copyright (C) 2016-2018  Jonas Bernoulli

;; Author: Jonas Bernoulli <jonas@bernoul.li>
;; Homepage: https://github.com/magit/ghub
;; Keywords: tools
;; Package-Requires: ((emacs "24.4") (let-alist "1.0.5"))

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

;; Ghub is a library that provides basic support for using the Github API
;; from Emacs packages.  It abstracts access to API resources using only
;; a handful of functions that are not resource-specific.

;; It also handles the creation, storage and use of access tokens using a
;; setup wizard, to make it easier for users to get started and to reduce
;; the support burden imposed on package maintainers.  It also comes with
;; a comprehensive manual to address the cases when things don't just
;; work as expected.

;; Ghub is intentionally limited to only provide these two essential
;; features — basic request functions and guided setup — to avoid being
;; too opinionated, which would hinder wide adaption.  It is assumed that
;; wide adoption would make life easier for users and maintainers alike,
;; because then all packages that talk to the Github API could be
;; configured the same way.

;;; Code:

(require 'auth-source)
(require 'cl-lib)
(require 'json)
(require 'let-alist)
(require 'url)
(require 'url-auth)

(eval-when-compile (require 'subr-x))

(defvar url-http-end-of-headers)
(defvar url-http-response-status)

;;; Settings

(defconst ghub-default-host "api.github.com")

(defvar ghub-github-token-scopes '(repo)
  "The Github API scopes that your private tools need.

The token that is created based on the value of this variable
is used when `ghub-request' (or one of its wrappers) is called
without providing a value for AUTH.  Packages should always
identify themselves using that argument, but when you use Ghub
directly in private tools, then that is not necessary and the
request is made on behalf of the `ghub' package itself, aka on
behalf of some private tool.

By default the only requested scope is `repo' because that is
sufficient as well as required for most common uses.  This and
other scopes are documented at https://magit.vc/goto/2e586d36.

If your private tools need other scopes, then you have to add
them here *before* creating the token.  Alternatively you can
edit the scopes of an existing token using the web interface
at https://github.com/settings/tokens.")

(defvar ghub-override-system-name nil
  "If non-nil, the string used to identify the local machine.
If this is nil, then the value returned by `system-name' is
used instead.")

;;; Request
;;;; API

(defvar ghub-response-headers nil
  "The headers returned in response to the last request.
`ghub-request' returns the response body and stores the
response header in this variable.")

(defvar ghub-raw-response-body nil)

(cl-defun ghub-head (resource &optional params
                              &key query payload headers
                              unpaginate noerror reader
                              username auth host)
  "Make a `HEAD' request for RESOURCE, with optional query PARAMS.
Like calling `ghub-request' (which see) with \"HEAD\" as METHOD."
  (ghub-request "HEAD" resource params
                :query query :payload payload :headers headers
                :unpaginate unpaginate :noerror noerror :reader reader
                :username username :auth auth :host host))

(cl-defun ghub-get (resource &optional params
                             &key query payload headers
                             unpaginate noerror reader
                             username auth host)
  "Make a `GET' request for RESOURCE, with optional query PARAMS.
Like calling `ghub-request' (which see) with \"GET\" as METHOD."
  (ghub-request "GET" resource params
                :query query :payload payload :headers headers
                :unpaginate unpaginate :noerror noerror :reader reader
                :username username :auth auth :host host))

(cl-defun ghub-put (resource &optional params
                             &key query payload headers
                             unpaginate noerror reader
                             username auth host)
  "Make a `PUT' request for RESOURCE, with optional payload PARAMS.
Like calling `ghub-request' (which see) with \"PUT\" as METHOD."
  (ghub-request "PUT" resource params
                :query query :payload payload :headers headers
                :unpaginate unpaginate :noerror noerror :reader reader
                :username username :auth auth :host host))

(cl-defun ghub-post (resource &optional params
                              &key query payload headers
                              unpaginate noerror reader
                              username auth host)
  "Make a `POST' request for RESOURCE, with optional payload PARAMS.
Like calling `ghub-request' (which see) with \"POST\" as METHOD."
  (ghub-request "POST" resource params
                :query query :payload payload :headers headers
                :unpaginate unpaginate :noerror noerror :reader reader
                :username username :auth auth :host host))

(cl-defun ghub-patch (resource &optional params
                               &key query payload headers
                               unpaginate noerror reader
                               username auth host)
  "Make a `PATCH' request for RESOURCE, with optional payload PARAMS.
Like calling `ghub-request' (which see) with \"PATCH\" as METHOD."
  (ghub-request "PATCH" resource params
                :query query :payload payload :headers headers
                :unpaginate unpaginate :noerror noerror :reader reader
                :username username :auth auth :host host))

(cl-defun ghub-delete (resource &optional params
                                &key query payload headers
                                unpaginate noerror reader
                                username auth host)
  "Make a `DELETE' request for RESOURCE, with optional payload PARAMS.
Like calling `ghub-request' (which see) with \"DELETE\" as METHOD."
  (ghub-request "DELETE" resource params
                :query query :payload payload :headers headers
                :unpaginate unpaginate :noerror noerror :reader reader
                :username username :auth auth :host host))

(define-error 'ghub-error "Ghub Error")
(define-error 'ghub-http-error "HTTP Error" 'ghub-error)
(define-error 'ghub-301 "Moved Permanently" 'ghub-http-error)
(define-error 'ghub-400 "Bad Request" 'ghub-http-error)
(define-error 'ghub-401 "Unauthorized" 'ghub-http-error)
(define-error 'ghub-403 "Forbidden" 'ghub-http-error)
(define-error 'ghub-404 "Not Found" 'ghub-http-error)
(define-error 'ghub-409 "Conflict" 'ghub-http-error)
(define-error 'ghub-422 "Unprocessable Entity" 'ghub-http-error)
(define-error 'ghub-500 "Internal Server Error" 'ghub-http-error)

(cl-defun ghub-request (method resource &optional params
                               &key query payload headers
                               unpaginate noerror reader
                               username auth host)
  "Make a request for RESOURCE and return the response body.

Also place the response header in `ghub-response-headers'.

METHOD is the http method, given as a string.
RESOURCE is the resource to access, given as a string beginning
  with a slash.

PARAMS, QUERY, PAYLOAD and HEADERS are alists used to specify
  data.  The Github API documentation is vague on how data has
  to be transmitted and for a particular resource usually just
  talks about \"parameters\".  Generally speaking when the METHOD
  is \"HEAD\" or \"GET\", then they have to be transmitted as a
  query, otherwise as a payload.
Use PARAMS to automatically transmit like QUERY or PAYLOAD would
  depending on METHOD.
Use QUERY to explicitly transmit data as a query.
Use PAYLOAD to explicitly transmit data as a payload.
Use HEADERS for those rare resources that require that the data
  is transmitted as headers instead of as a query or payload.
  When that is the case, then the api documentation usually
  mentions it explicitly.

If UNPAGINATE is non-nil, then make multiple requests if necessary
  to get all items at RESOURCE.
If NOERROR is non-nil, then do not raise an error if the request
  fails and return nil instead.
If READER is non-nil, then it is used to read and return from the
  response buffer.  The default is `ghub--read-json-response'.
  For the very few resources that do not return json, you might
  want to use `ghub--read-raw-response'.

If USERNAME is non-nil, then make a request on behalf of that
  user.  It is better to specify the user using the Git variable
  `github.user' for \"api.github.com\", or `github.HOST.user' if
  connecting to a Github Enterprise instance.

Each package that uses `ghub' should use its own token. If AUTH
  is nil, then the generic `ghub' token is used instead.  This
  is only acceptable for personal utilities.  A packages that
  is distributed to other users should always use this argument
  to identify itself, using a symbol matching its name.

  Package authors who find this inconvenient should write a
  wrapper around this function and possibly for the method
  specific functions also.

  Some symbols have a special meaning.  `none' means to make an
  unauthorized request.  `basic' means to make a password based
  request.  If the value is a string, then it is assumed to be
  a valid token.  `basic' and an explicit token string are only
  intended for internal and debugging uses.

  If AUTH is a package symbol, then the scopes are specified
  using the variable `AUTH-github-token-scopes'.  It is an error
  if that is not specified.  See `ghub-github-token-scopes' for
  an example.

If HOST is non-nil, then connect to that Github instance.  This
  defaults to \"api.github.com\".  When a repository is connected
  to a Github Enterprise instance, then it is better to specify
  that using the Git variable `github.host' instead of using this
  argument."
  (unless (string-prefix-p "/" resource)
    (setq resource (concat "/" resource)))
  (unless host
    (setq host (ghub--host)))
  (cond
   ((not params))
   ((memq method '("GET" "HEAD"))
    (when query
      (error "PARAMS and QUERY are mutually exclusive for METHOD %S" method))
    (setq query params))
   (t
    (when payload
      (error "PARAMS and PAYLOAD are mutually exclusive for METHOD %S" method))
    (setq payload params)))
  (when (and payload (not (stringp payload)))
    (setq payload (encode-coding-string (json-encode-list payload) 'utf-8)))
  (let* ((qry (and query (concat "?" (ghub--url-encode-params query))))
         (buf (let ((url-request-extra-headers
                     `(("Content-Type" . "application/json")
                       ,@(and (not (eq auth 'none))
                              (list (cons "Authorization"
                                          (ghub--auth host auth username))))
                       ,@headers))
                    ;; Encode in case caller used (symbol-name 'GET).  #35
                    (url-request-method (encode-coding-string method 'utf-8))
                    (url-request-data payload))
                (url-retrieve-synchronously
                 (concat "https://" host resource qry)))))
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
            (setq body (funcall (or reader 'ghub--read-json-response)
                                url-http-response-status))
            (unless (or noerror (= (/ url-http-response-status 100) 2))
              (let ((data (list method resource qry payload body)))
                (pcase url-http-response-status
                  (301 (signal 'ghub-301 data))
                  (400 (signal 'ghub-400 data))
                  (401 (signal 'ghub-401 data))
                  (403 (signal 'ghub-403 data))
                  (404 (signal 'ghub-404 data))
                  (409 (signal 'ghub-409 data))
                  (422 (signal 'ghub-422 data))
                  (500 (signal 'ghub-500 data))
                  (_   (signal 'ghub-http-error
                               (cons url-http-response-status data))))))
            (if (and link unpaginate)
                (nconc body
                       (ghub-request
                        method resource nil
                        :query (cons (cons 'page link)
                                     (cl-delete 'page query :key #'car))
                        :payload payload
                        :headers headers
                        :unpaginate t :noerror noerror :reader reader
                        :username username :auth auth :host host))
              body)))
      (kill-buffer buf))))

(defun ghub-wait (resource &optional username auth host duration)
  "Busy-wait up to DURATION seconds for RESOURCE to become available.

DURATION specifies how many seconds to wait at most.  It defaults
to 64 seconds.  The first attempt is made immediately, the second
after two seconds, and each subequent attemts are made after
waiting as long as we already waited between all preceding
attempts combined.

See `ghub-request' for information about the other arguments."
  (unless duration
    (setq duration 64))
  (with-local-quit
    (let ((total 0))
      (while (not (ignore-errors (ghub-get resource nil
                                           :username username
                                           :auth auth
                                           :host host)))
        (message "Waited (%3ss of %ss) for %s..." total duration resource)
        (if (= total duration)
            (signal 'ghub-error
                    (list (format "Github is taking too long to create %s"
                                  resource)))
          (if (> total 0)
              (let ((wait (min total (- duration total))))
                (sit-for wait)
                (cl-incf total wait))
            (sit-for (setq total 2))))))))

;;;; Internal

(defun ghub--read-json-response (status)
  (let ((raw (ghub--read-raw-response)))
    (and raw
         (condition-case nil
             (let ((json-object-type 'alist)
                   (json-array-type  'list)
                   (json-key-type    'symbol)
                   (json-false       nil)
                   (json-null        nil))
               (json-read-from-string raw))
           (json-readable-error
            (ghub--handle-invalid-response status raw))))))

(defun ghub--read-raw-response (&optional _status)
  (and (not (eobp))
       (setq ghub-raw-response-body
             (decode-coding-string
              (buffer-substring-no-properties (point) (point-max))
              'utf-8))))

(defun ghub--handle-invalid-response (status body)
  (let ((html-p (string-prefix-p "<!DOCTYPE html>" body))
        content)
    (when html-p
      (with-temp-buffer
        (save-excursion (insert body))
        (while (re-search-forward "<p>\\(?:<strong>\\)?\\([^<]+\\)" nil t)
          (push (match-string 1) content)))
      (when content
        (setq content (mapconcat #'identity (reverse content) " "))))
    `((http_status      . ,status)
      (invalid_response . "Github failed to deliver Json.")
      (invalid_is_html  . ,html-p)
      (invalid_comment  . "Message consists of strings found in the html.")
      (message          . ,content))))

(defun ghub--url-encode-params (params)
  (mapconcat (lambda (param)
               (concat (url-hexify-string (symbol-name (car param))) "="
                       (url-hexify-string (cdr param))))
             params "&"))

;;; Authentication
;;;; API

;;;###autoload
(defun ghub-create-token (host username package scopes)
  "Create, store and return a new token.

HOST is the Github instance, usually \"api.github.com\".
USERNAME is the name of a user on that instance.
PACKAGE is the package that will use the token.
SCOPES are the scopes the token is given access to."
  (interactive
   (pcase-let ((`(,host ,username ,package)
                (ghub--read-triplet)))
     (list host username package
           (split-string
            (read-string
             "Scopes (separated by commas): "
             (mapconcat #'symbol-name
                        (symbol-value
                         (intern (format "%s-github-token-scopes" package)))
                        ","))
            "," t "[\s\t]+"))))
  (let ((user (ghub--ident username package)))
    (cl-destructuring-bind (_save token)
        (ghub--auth-source-get (list :save-function :secret)
          :create t :host host :user user
          :secret
          (cdr (assq 'token
                     (ghub-post
                      "/authorizations"
                      `((scopes . ,scopes)
                        (note   . ,(ghub--ident-github package)))
                      :username username :auth 'basic :host host))))
      ;; If the Auth-Source cache contains the information that there
      ;; is no value, then setting the value does not invalidate that
      ;; now incorrect information.
      (auth-source-forget (list :host host :user user))
      token)))

;;;###autoload
(defun ghub-token-scopes (host username package)
  "Return and echo the scopes of the specified token.
This is intended for debugging purposes only.  The user
has to provide several values including their password."
  (interactive (ghub--read-triplet))
  (let ((scopes
         (cdr (assq 'scopes (ghub--get-token-plist host username package)))))
    (when (called-interactively-p 'any)
      ;; Also show the input values to make it easy for package
      ;; authors to verify that the user has done it correctly.
      (message "Scopes for %s@%s: %S"
               (ghub--ident username package)
               host scopes))
    scopes))

;;;; Internal

(defun ghub--auth (host auth &optional username)
  (unless username
    (setq username (ghub--username host)))
  (if (eq auth 'basic)
      (ghub--basic-auth host username)
    (concat "token "
            (encode-coding-string
             (cl-typecase auth
               (string auth)
               (null   (ghub--token host username 'ghub))
               (symbol (ghub--token host username auth))
               (t (signal 'wrong-type-argument
                          `((or stringp symbolp) ,auth))))
             'utf-8))))

(defun ghub--basic-auth (host username)
  (let ((url (url-generic-parse-url (concat "https://" host))))
    (setf (url-user url) username)
    (url-basic-auth url t)))

(defun ghub--token (host username package &optional nocreate)
  (let ((user (ghub--ident username package)))
    (or (ghub--auth-source-get :secret :host host :user user)
        (progn
          ;; Auth-Source caches the information that there is no
          ;; value, but in our case that is a situation that needs
          ;; fixing so we want to keep trying by invalidating that
          ;; information.  The (:max 1) is needed for Emacs releases
          ;; before 26.1.
          (auth-source-forget (list :max 1 :host host :user
          user))
          (and (not nocreate)
               (ghub--confirm-create-token host username package))))))

(defun ghub--host ()
  (or (ignore-errors (car (process-lines "git" "config" "github.host")))
      ghub-default-host))

(defun ghub--username (host)
  (let ((var (if (string-prefix-p "api.github.com" host)
                 "github.user"
               (format "github.%s.user" host))))
    (condition-case nil
        (car (process-lines "git" "config" var))
      (error
       (let ((user (read-string
                    (format "Git variable `%s' is unset.  Set to: " var))))
         (or (and user (progn (call-process "git" nil nil nil
                                            "config" "--global" var user)
                              user))
             (user-error "Abort")))))))

(defun ghub--ident (username package)
  (format "%s^%s" username package))

(defun ghub--ident-github (package)
  (format "Emacs package %s @ %s"
          package
          (or ghub-override-system-name (system-name))))

(defun ghub--package-scopes (package)
  (symbol-value (intern (format "%s-github-token-scopes" package))))

(defun ghub--confirm-create-token (host username package)
  (let* ((ident (ghub--ident-github package))
         (scopes (ghub--package-scopes package))
         (max-mini-window-height 40))
    (if (let ((message-log-max nil))
          (yes-or-no-p
           (format
            "Such a Github API token is not available:

  Host:    %s
  User:    %s
  Package: %s

  Scopes requested in `%s-github-token-scopes':\n%s
  Store locally according to `auth-sources':\n    %S
  Store on Github as:\n    %S

WARNING: If you have enabled two-factor authentication then
         you have to abort and create the token manually.

If in doubt, then abort and first view the section of the Ghub
documentation called \"Manually Creating and Storing a Token\".

Otherwise confirm and then provide your Github username and
password at the next two prompts.  Depending on the backend
you might have to provide a passphrase and confirm that you
really want to save the token.

Create and store such a token? "
            host username package package
            (mapconcat (lambda (scope) (format "    %s" scope)) scopes "\n")
            auth-sources ident)))
        (progn
          (when (ghub--get-token-id host username package)
            (if (yes-or-no-p
                 (format
                  "A token named %S\nalready exists on Github.  Replace it?"
                  ident))
                (ghub--delete-token host username package)
              (user-error "Abort")))
          (ghub-create-token host username package scopes))
      (user-error "Abort"))))

(defun ghub--get-token-id (host username package)
  (let ((ident (ghub--ident-github package)))
    (cl-some (lambda (x)
               (let-alist x
                 (and (equal .app.name ident) .id)))
             (ghub-get "/authorizations" nil
                       :unpaginate t
                       :username username :auth 'basic :host host))))

(defun ghub--get-token-plist (host username package)
  (ghub-get (format "/authorizations/%s"
                    (ghub--get-token-id host username package))
            nil :username username :auth 'basic :host host))

(defun ghub--delete-token (host username package)
  (ghub-delete (format "/authorizations/%s"
                       (ghub--get-token-id host username package))
               nil :username username :auth 'basic :host host))

(defun ghub--read-triplet ()
  (let ((host (read-string "Host: " (ghub--host))))
    (list host
          (read-string "Username: " (ghub--username host))
          (intern (read-string "Package: " "ghub")))))

(defun ghub--auth-source-get (key:s &rest spec)
  (declare (indent 1))
  (let ((plist (car (apply #'auth-source-search :max 1 spec))))
    (cl-flet ((value (k) (let ((v (plist-get plist k)))
                           (if (functionp v) (funcall v) v))))
      (if (listp key:s)
          (mapcar #'value key:s)
        (value key:s)))))

(advice-add 'auth-source-netrc-parse-next-interesting :around
            'auth-source-netrc-parse-next-interesting@save-match-data)
(defun auth-source-netrc-parse-next-interesting@save-match-data (fn)
  "Save match-data for the benefit of caller `auth-source-netrc-parse-one'.
Without wrapping this function in `save-match-data' the caller
won't see the secret from a line that is followed by a commented
line."
  (save-match-data (funcall fn)))

;;; ghub.el ends soon
(provide 'ghub)
;; Local Variables:
;; indent-tabs-mode: nil
;; End:
;;; ghub.el ends here
