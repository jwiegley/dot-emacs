;;; auth-password-store-tests.el --- Tests for auth-password-store.el  -*- lexical-binding: t; -*-

;; Copyright (C) 2013 Damien Cassou

;; Author: Damien Cassou <damien.cassou@gmail.com>

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

;; Tests for auth-password-store.el

;;; Code:

(require 'ert)

(require 'auth-password-store)

(eval-when-compile (require 'cl-macs))

(ert-deftest parse-simple ()
  (let ((content "pass\nkey1:val1\nkey2:val2\n"))
    (should (equal (auth-pass--parse-data content)
                   '(("key1" . "val1")
                     ("key2" . "val2"))))))

(ert-deftest parse-with-dash-line ()
  (let ((content "pass\n--\nkey1:val1\nkey2:val2\n"))
    (should (equal (auth-pass--parse-data content)
                   '(("key1" . "val1")
                     ("key2" . "val2"))))))

(ert-deftest parse-with-trailing-spaces ()
  (let ((content "pass\n--\nkey1 :val1   \nkey2:   val2\n\n"))
    (should (equal (auth-pass--parse-data content)
                   '(("key1" . "val1")
                     ("key2" . "val2"))))))

(defvar auth-pass--debug-log nil
  "Contains a list of all messages passed to `auth-source-do-debug`.")

(defun should-have-message-containing (regexp)
  "Assert that at least one `auth-source-do-debug` matched REGEXP."
  (should (seq-find (lambda (message)
                      (string-match regexp message))
                    auth-pass--debug-log)))

(defun auth-pass-debug (&rest msg)
  "Format MSG and add that to `auth-pass--debug-log`.
This function is intended to be set to `auth-source-debug`."
  (add-to-list 'auth-pass--debug-log (apply #'format msg) t))

(defmacro auth-pass-deftest (name arglist store &rest body)
  "Define a new ert-test NAME with ARGLIST using STORE as password-store.
BODY is a sequence of instructions that will be evaluated.

This macro overrides `auth-pass-parse-entry' and `password-store-list' to
test code without touching the file system."
  (declare (indent 3))
  `(ert-deftest ,name ,arglist
     (cl-letf (((symbol-function 'auth-pass-parse-entry) (lambda (entry) (cdr (cl-find entry ,store :key #'car :test #'string=))) )
               ((symbol-function 'password-store-list) (lambda () (mapcar #'car ,store)))
               ((symbol-function 'auth-pass--entry-valid-p) (lambda (_entry) t)))
       (let ((auth-source-debug #'auth-pass-debug)
             (auth-pass--debug-log nil))
         ,@body))))

(auth-pass-deftest find-match-matching-at-entry-name ()
                   '(("foo"))
  (should (equal (auth-pass--find-match "foo" nil nil)
                 "foo")))

(auth-pass-deftest find-match-matching-at-entry-name-part ()
                   '(("foo"))
  (should (equal (auth-pass--find-match "https://foo" nil nil)
                 "foo")))

(auth-pass-deftest find-match-matching-at-entry-name-ignoring-user ()
                   '(("foo"))
  (should (equal (auth-pass--find-match "https://SomeUser@foo" nil nil)
                 "foo")))

(auth-pass-deftest find-match-matching-at-entry-name-with-user ()
                   '(("SomeUser@foo"))
  (should (equal (auth-pass--find-match "https://SomeUser@foo" nil nil)
                 "SomeUser@foo")))

(auth-pass-deftest find-match-matching-at-entry-name-prefer-full ()
                   '(("SomeUser@foo") ("foo"))
  (should (equal (auth-pass--find-match "https://SomeUser@foo" nil nil)
                 "SomeUser@foo")))

;; same as previous one except the store is in another order
(auth-pass-deftest find-match-matching-at-entry-name-prefer-full-reversed ()
                   '(("foo") ("SomeUser@foo"))
  (should (equal (auth-pass--find-match "https://SomeUser@foo" nil nil)
                 "SomeUser@foo")))

(auth-pass-deftest find-match-matching-at-entry-name-without-subdomain ()
                   '(("bar.com"))
  (should (equal (auth-pass--find-match "foo.bar.com" nil nil)
                 "bar.com")))

(auth-pass-deftest find-match-matching-at-entry-name-without-subdomain-with-user ()
                   '(("someone@bar.com"))
  (should (equal (auth-pass--find-match "foo.bar.com" "someone" nil)
                 "someone@bar.com")))

(auth-pass-deftest find-match-matching-at-entry-name-without-subdomain-with-bad-user ()
                   '(("someoneelse@bar.com"))
  (should (equal (auth-pass--find-match "foo.bar.com" "someone" nil)
                 nil)))

(auth-pass-deftest find-match-matching-at-entry-name-without-subdomain-prefer-full ()
                   '(("bar.com") ("foo.bar.com"))
  (should (equal (auth-pass--find-match "foo.bar.com" nil nil)
                 "foo.bar.com")))

(auth-pass-deftest dont-match-at-folder-name ()
                   '(("foo.bar.com/foo"))
  (should (equal (auth-pass--find-match "foo.bar.com" nil nil)
                 nil)))

(auth-pass-deftest find-match-matching-extracting-user-from-host ()
                   '(("foo.com/bar"))
  (should (equal (auth-pass--find-match "https://bar@foo.com" nil nil)
                 "foo.com/bar")))

(auth-pass-deftest search-with-user-first ()
                   '(("foo") ("user@foo"))
  (should (equal (auth-pass--find-match "foo" "user" nil)
                 "user@foo"))
  (should-have-message-containing "Found 1 match"))

(auth-pass-deftest give-priority-to-desired-user ()
                   '(("foo") ("subdir/foo" ("user" . "someone")))
  (should (equal (auth-pass--find-match "foo" "someone" nil)
                 "subdir/foo"))
  (should-have-message-containing "Found 2 matches")
  (should-have-message-containing "matching user field"))

(auth-pass-deftest give-priority-to-desired-user-reversed ()
                   '(("foo" ("user" . "someone")) ("subdir/foo"))
  (should (equal (auth-pass--find-match "foo" "someone" nil)
                 "foo"))
  (should-have-message-containing "Found 2 matches")
  (should-have-message-containing "matching user field"))

(auth-pass-deftest return-first-when-several-matches ()
                   '(("foo") ("subdir/foo"))
  (should (equal (auth-pass--find-match "foo" nil nil)
                 "foo"))
  (should-have-message-containing "Found 2 matches")
  (should-have-message-containing "the first one"))

(auth-pass-deftest make-divansantana-happy ()
                   '(("host.com"))
  (should (equal (auth-pass--find-match "smtp.host.com" "myusername@host.co.za" nil)
                 "host.com")))

(auth-pass-deftest find-host-without-port ()
                   '(("host.com"))
  (should (equal (auth-pass--find-match "host.com:8888" "someuser" nil)
                 "host.com")))

(defmacro auth-pass-deftest-build-result (name arglist store &rest body)
  "Define a new ert-test NAME with ARGLIST using STORE as password-store.
BODY is a sequence of instructions that will be evaluated.

This macro overrides `auth-pass-parse-entry', `password-store-list', and
`auth-pass--find-match' to ease testing."
  (declare (indent 3))
  `(auth-pass-deftest ,name ,arglist ,store
     (cl-letf (((symbol-function 'auth-pass-find-match)
                (lambda (_host _user)
                  "foo")))
       ,@body)))

(auth-pass-deftest-build-result build-result-return-parameters ()
                                '(("foo"))
  (let ((result (auth-pass--build-result "foo" 512 "user")))
    (should (equal (plist-get result :port) 512))
    (should (equal (plist-get result :user) "user"))))

(auth-pass-deftest-build-result build-result-return-entry-values ()
                                '(("foo" ("port" . 512) ("user" . "anuser")))
  (let ((result (auth-pass--build-result "foo" nil nil)))
    (should (equal (plist-get result :port) 512))
    (should (equal (plist-get result :user) "anuser"))))

(auth-pass-deftest-build-result build-result-entry-takes-precedence ()
                                '(("foo" ("port" . 512) ("user" . "anuser")))
  (let ((result (auth-pass--build-result "foo" 1024 "anotheruser")))
    (should (equal (plist-get result :port) 512))
    (should (equal (plist-get result :user) "anuser"))))

(ert-deftest build-result-passes-full-host-to-find-match ()
  (let (passed-host)
    (cl-letf (((symbol-function 'auth-pass--find-match)
               (lambda (host _user _port) (setq passed-host host))))
      (auth-pass--build-result "https://user@host.com:123" nil nil)
      (should (equal passed-host "https://user@host.com:123"))
      (auth-pass--build-result "https://user@host.com" nil nil)
      (should (equal passed-host "https://user@host.com"))
      (auth-pass--build-result "user@host.com" nil nil)
      (should (equal passed-host "user@host.com"))
      (auth-pass--build-result "user@host.com:443" nil nil)
      (should (equal passed-host "user@host.com:443")))))

(ert-deftest only-return-entries-that-can-be-open ()
  (cl-letf (((symbol-function 'password-store-list)
             (lambda () '("foo.site.com" "bar.site.com" "mail/baz.site.com/scott")))
            ((symbol-function 'auth-pass--entry-valid-p)
             ;; only foo.site.com and mail/baz.site.com/scott are valid
             (lambda (entry) (member entry '("foo.site.com" "mail/baz.site.com/scott")))))
    (should (equal (auth-pass--find-all-by-entry-name "foo.site.com" "someuser")
                   '("foo.site.com")))
    (should (equal (auth-pass--find-all-by-entry-name "bar.site.com" "someuser")
                   '()))
    (should (equal (auth-pass--find-all-by-entry-name "baz.site.com" "scott")
                   '("mail/baz.site.com/scott")))))

(ert-deftest entry-is-not-valid-when-unreadable ()
  (cl-letf (((symbol-function 'password-store--run-show)
             (lambda (entry)
               ;; only foo is a valid entry
               (if (string-equal entry "foo")
                   "password"
                 nil))))
    (should (auth-pass--entry-valid-p "foo"))
    (should-not (auth-pass--entry-valid-p "bar"))))

(provide 'auth-password-store-tests)

;;; auth-password-store-tests.el ends here
