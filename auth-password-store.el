;;; auth-password-store.el --- Integrate auth-source with password-store -*- lexical-binding: t -*-

;; Copyright (C) 2015 Damien Cassou & Nicolas Petton

;; Author: Damien Cassou <damien@cassou.me>,
;;         Nicolas Petton <nicolas@petton.fr>
;; Version: 0.1
;; GIT: https://github.com/DamienCassou/auth-password-store
;; Package-Requires: ((emacs "24.4") (password-store "0.1") (seq "1.9") (cl-lib "0.5"))
;; Created: 07 Jun 2015
;; Keywords: pass password-store auth-source username password login

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
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

;; Integrate Emacs' auth-source with password-store

;;; Code:
(require 'seq)
(require 'subr-x)
(require 'cl-lib)
(require 'cl-macs)
(require 'auth-source)
(require 'password-store)
(require 'url-parse)

(cl-defun auth-pass-search (&rest spec
                                  &key backend type host user port
                                  &allow-other-keys)
  "Given a property list SPEC, return search matches from the :backend.
See `auth-source-search' for details on SPEC."
  (cl-assert (or (null type) (eq type (oref backend type)))
             t "Invalid password-store search: %s %s")
  (when (listp host)
    ;; Take the first non-nil item of the list of hosts
    (setq host (seq-find #'identity host)))
  (list (auth-pass--build-result host port user)))

(defun auth-pass--build-result (host port user)
  "Build auth-pass entry matching HOST, PORT and USER."
  (let ((entry (auth-pass--find-match host user port)))
    (when entry
      (let ((retval (list
                     :host host
                     :port (or (auth-pass-get "port" entry) port)
                     :user (or (auth-pass-get "user" entry) user)
                     :secret (lambda () (auth-pass-get 'secret entry)))))
        (auth-pass--do-debug "return %s as final result (plus hidden password)"
                             (seq-subseq retval 0 -2)) ;; remove password
        retval))))

;;;###autoload
(defun auth-pass-enable ()
  "Enable auth-password-store."
  ;; To add password-store to the list of sources, evaluate the following:
  (add-to-list 'auth-sources 'password-store)
  ;; clear the cache (required after each change to #'auth-pass-search)
  (auth-source-forget-all-cached))

(defvar auth-pass-backend
  (auth-source-backend "password-store"
                       :source "." ;; not used
                       :type 'password-store
                       :search-function #'auth-pass-search)
  "Auth-source backend for password-store.")

(defun auth-pass-backend-parse (entry)
  "Create a password-store auth-source backend from ENTRY."
  (when (eq entry 'password-store)
    (auth-source-backend-parse-parameters entry auth-pass-backend)))

(advice-add 'auth-source-backend-parse :before-until #'auth-pass-backend-parse)


(defun auth-pass-get (key entry)
  "Return the value associated to KEY in the password-store entry ENTRY.

ENTRY is the name of a password-store entry.
The key used to retrieve the password is the symbol `secret'.

The convention used as the format for a password-store file is
the following (see http://www.passwordstore.org/#organization):

secret
key1: value1
key2: value2"
  (let ((data (auth-pass-parse-entry entry)))
    (or (cdr (assoc key data))
        (and (string= key "user")
             (cdr (assoc "username" data))))))

(defun auth-pass-parse-entry (entry)
  "Return an alist of the data associated with ENTRY.

ENTRY is the name of a password-store entry."
  (let ((file-contents (ignore-errors (password-store--run-show entry))))
    (and file-contents
         (cons `(secret . ,(auth-pass--parse-secret file-contents))
               (auth-pass--parse-data file-contents)))))

(defun auth-pass--parse-secret (contents)
    "Parse the password-store data in the string CONTENTS and return its secret.
The secret is the first line of CONTENTS."
  (car (split-string contents "\\\n" t)))

(defun auth-pass--parse-data (contents)
  "Parse the password-store data in the string CONTENTS and return an alist.
CONTENTS is the contents of a password-store formatted file."
  (let ((lines (split-string contents "\\\n" t "\\\s")))
    (seq-remove #'null
                (mapcar (lambda (line)
                          (let ((pair (mapcar #'string-trim
                                              (split-string line ":"))))
                            (when (> (length pair) 1)
                              (cons (car pair)
                                    (mapconcat #'identity (cdr pair) ":")))))
                        (cdr lines)))))

(defun auth-pass--remove-directory-name (name)
  "Remove directories from NAME.
E.g., if NAME is \"foo/bar\", return \"bar\"."
  (replace-regexp-in-string ".*/" "" name))

(defun auth-pass--do-debug (&rest msg)
  "Call `auth-source-do-debug` with MSG and a prefix."
  (apply #'auth-source-do-debug
         (cons (concat "auth-password-store: " (car msg))
               (cdr msg))))

(defun auth-pass--select-one-entry (entries user)
  "Select one entry from ENTRIES by searching for a field matching USER."
  (let ((number (length entries))
        (entry-with-user
         (and user
              (seq-find (lambda (entry)
                          (string-equal (auth-pass-get "user" entry) user))
                        entries))))
    (auth-pass--do-debug "found %s matches: %s" number
                         (mapconcat #'identity entries ", "))
    (if entry-with-user
        (progn
          (auth-pass--do-debug "return %s as it contains matching user field"
                               entry-with-user)
          entry-with-user)
      (auth-pass--do-debug "return %s as it is the first one" (car entries))
      (car entries))))

(defun auth-pass--entry-valid-p (entry)
  "Return t iff ENTRY can be opened.
Also displays a warning if not.  This function is slow, don't call it too
often."
  (if (auth-pass-parse-entry entry)
      t
    (auth-pass--do-debug "entry '%s' is not valid" entry)
    nil))

(defun auth-pass--find-all-by-entry-name (entryname user)
  "Search the store for all entries either matching ENTRYNAME/USER or ENTRYNAME.
Only return valid entries as of `auth-pass--entry-valid-p'."
  (seq-filter (lambda (entry)
                (and
                 (or
                  (let ((components-host-user
                         (member entryname (split-string entry "/"))))
                    (and (= (length components-host-user) 2)
                         (string-equal user (cadr components-host-user))))
                  (string-equal entryname (auth-pass--remove-directory-name entry)))
                 (auth-pass--entry-valid-p entry)))
              (password-store-list)))

(defun auth-pass--find-one-by-entry-name (entryname user)
  "Search the store for an entry matching ENTRYNAME.
If USER is non nil, give precedence to entries containing a user field
matching USER."
  (auth-pass--do-debug "searching for '%s' in entry names (user: %s)"
                       entryname
                       user)
  (let ((matching-entries (auth-pass--find-all-by-entry-name entryname user)))
    (pcase (length matching-entries)
      (0 (auth-pass--do-debug "no match found")
         nil)
      (1 (auth-pass--do-debug "found 1 match: %s" (car matching-entries))
         (car matching-entries))
      (_ (auth-pass--select-one-entry matching-entries user)))))

(defun auth-pass--find-match (host user port)
  "Return a password-store entry name matching HOST, USER and PORT.
Disambiguate between user provided inside HOST (e.g., user@server.com) and
inside USER by giving priority to USER.  Same for PORT."
  (let* ((url (url-generic-parse-url (if (string-match-p ".*://" host)
                                         host
                                       (format "https://%s" host)))))
    (auth-pass--find-match-unambiguous
     (or (url-host url) host)
     (or user (url-user url))
     ;; url-port returns 443 (because of the https:// above) by default
     (or port (number-to-string (url-port url))))))

(defun auth-pass--find-match-unambiguous (hostname user port)
  "Return a password-store entry name matching HOSTNAME, USER and PORT.
If many matches are found, return the first one.  If no match is
found, return nil.

HOSTNAME should not contain any username or port number."
  (or
   (and user port (auth-pass--find-one-by-entry-name (format "%s@%s:%s" user hostname port) user))
   (and user (auth-pass--find-one-by-entry-name (format "%s@%s" user hostname) user))
   (and port (auth-pass--find-one-by-entry-name (format "%s:%s" hostname port) nil))
   (auth-pass--find-one-by-entry-name hostname user)
   ;; if that didn't work, remove subdomain: foo.bar.com -> bar.com
   (let ((components (split-string hostname "\\.")))
     (when (= (length components) 3)
       ;; start from scratch
       (auth-pass--find-match-unambiguous
        (mapconcat 'identity (cdr components) ".")
        user
        port)))))

(provide 'auth-password-store)
;;; auth-password-store.el ends here
