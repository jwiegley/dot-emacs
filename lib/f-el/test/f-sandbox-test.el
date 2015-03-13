;;; f-sandbox-test.el --- F: Sandbox tests  -*- lexical-binding: t; -*-

;; Copyright (C) 2014 Johan Andersson

;; Author: Johan Andersson <johan.rejeep@gmail.com>
;; Maintainer: Johan Andersson <johan.rejeep@gmail.com>
;; URL: http://github.com/rejeep/f.el

;; This file is NOT part of GNU Emacs.

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

;;; Code:



(eval-when-compile
  (defvar f-test/playground-path)
  (defvar f-test/trash-path))


;;;; f-write-bytes

(ert-deftest f-guard-test/f-write-bytes/same ()
  (with-playground
   (let ((path (f-expand "foo.txt" f-test/playground-path)))
     (f-with-sandbox path
       (let ((bytes (unibyte-string 1 2 3)))
         (f-write-bytes bytes path)
         (should-exist path bytes))))))

(ert-deftest f-guard-test/f-write-bytes/inside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (let ((bytes (unibyte-string 1 2 3)))
       (f-write-bytes bytes "foo.txt")
       (should-exist "foo.txt" bytes)))))

(ert-deftest f-guard-test/f-write-bytes/outside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (let ((bytes (unibyte-string 1 2 3))
           (default-directory f-test/trash-path))
       (should-error (f-write-bytes bytes "foo.txt") :type 'f-guard-error)))))


;;;; f-write-text

(ert-deftest f-guard-test/f-write-text/same ()
  (with-playground
   (let ((path (f-expand "foo.txt" f-test/playground-path)))
     (f-with-sandbox path
       (f-write-text "foo" 'utf-8 path)
       (should-exist path "foo")))))

(ert-deftest f-guard-test/f-write-text/inside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (f-write-text "foo" 'utf-8 "foo.txt")
     (should-exist "foo.txt" "foo"))))

(ert-deftest f-guard-test/f-write-text/outside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (let ((default-directory f-test/trash-path))
       (should-error (f-write-text "foo" 'utf-8 "foo.txt") :type 'f-guard-error)))))


;;;; f-mkdir

(ert-deftest f-guard-test/f-mkdir/same ()
  (with-playground
   (let ((path (f-expand "foo" f-test/playground-path)))
     (f-with-sandbox path
       (f-mkdir path)
       (should-exist path)))))

(ert-deftest f-guard-test/f-mkdir/inside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (f-mkdir "foo")
     (should-exist "foo"))))

(ert-deftest f-guard-test/f-mkdir/outside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (let ((default-directory f-test/trash-path))
       (should-error (f-mkdir "foo") :type 'f-guard-error)))))


;;;; f-delete

(ert-deftest f-guard-test/f-delete/same ()
  (with-playground
   (let ((path (f-expand "foo" f-test/playground-path)))
     (f-touch path)
     (f-with-sandbox path
       (f-delete path)
       (should-not-exist path)))))

(ert-deftest f-guard-test/f-delete/inside ()
  (with-playground
   (f-touch "foo")
   (f-with-sandbox f-test/playground-path
     (f-delete "foo")
     (should-not-exist "foo"))))

(ert-deftest f-guard-test/f-delete/outside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (let ((default-directory f-test/trash-path))
       (should-error (f-delete "foo") :type 'f-guard-error)))))


;;;; f-symlink

(ert-deftest f-guard-test/f-symlink/same ()
  (with-playground
   (let ((path-foo (f-expand "foo" f-test/playground-path))
         (path-bar (f-expand "bar" f-test/playground-path)))
     (f-with-sandbox (list path-foo path-bar)
       (f-touch path-foo)
       (f-symlink path-foo path-bar)
       (should-exist path-bar)))))

(ert-deftest f-guard-test/f-symlink/inside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (f-touch "foo")
     (f-symlink "foo" "bar")
     (should-exist "bar"))))

(ert-deftest f-guard-test/f-symlink/outside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (let ((default-directory f-test/trash-path))
       (should-error (f-symlink "foo" "bar") :type 'f-guard-error)))))


;;;; f-move

(ert-deftest f-guard-test/f-move/same ()
  (with-playground
   (let ((path-foo (f-expand "foo" f-test/playground-path))
         (path-bar (f-expand "bar" f-test/playground-path)))
     (f-with-sandbox (list path-foo path-bar)
       (f-touch path-foo)
       (f-move path-foo path-bar)
       (should-exist path-bar)
       (should-not-exist path-foo)))))

(ert-deftest f-guard-test/f-move/inside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (f-touch "foo")
     (f-move "foo" "bar")
     (should-exist "bar")
     (should-not-exist "foo"))))

(ert-deftest f-guard-test/f-move/outside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (let ((default-directory f-test/trash-path))
       (should-error (f-move "foo" "bar") :type 'f-guard-error)))))


;;;; f-copy

(ert-deftest f-guard-test/f-copy/inside ()
  (with-playground
   (let ((path-foo (f-expand "foo" f-test/playground-path))
         (path-bar (f-expand "bar" f-test/playground-path)))
     (f-with-sandbox (list path-foo path-bar)
       (f-touch path-foo)
       (f-copy path-foo path-bar)
       (should-exist path-foo)
       (should-exist path-bar)))))

(ert-deftest f-guard-test/f-copy/inside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (f-touch "foo")
     (f-copy "foo" "bar")
     (should-exist "foo")
     (should-exist "bar"))))

(ert-deftest f-guard-test/f-copy/outside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (let ((default-directory f-test/trash-path))
       (should-error (f-copy "foo" "bar") :type 'f-guard-error)))))


;;;; f-touch

(ert-deftest f-guard-test/f-touch/same ()
  (with-playground
   (let ((path (f-expand "foo" f-test/playground-path)))
     (f-with-sandbox path
       (f-touch path)
       (should-exist path)))))

(ert-deftest f-guard-test/f-touch/inside ()
  (with-playground
   (f-with-sandbox f-test/playground-path
     (f-touch "foo")
     (should-exist "foo"))))

(ert-deftest f-guard-test/f-touch/outside ()
  (with-playground
   (f-touch (f-expand "foo" f-test/trash-path))
   (f-with-sandbox f-test/playground-path
     (let ((default-directory f-test/trash-path))
       (should-error (f-touch "foo") :type 'f-guard-error)))))

(provide 'f-sandbox-test)

;;; f-sandbox-test.el ends here
