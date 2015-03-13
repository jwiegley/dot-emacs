;;; f-destructive-test.el --- F: Test for destructive functions  -*- lexical-binding: t; -*-

;; Copyright (C) 2013-2014 Johan Andersson

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


;;;; f-mkdir

(ert-deftest f-mkdir-test/single-level ()
  (with-playground
   (f-mkdir "foo")
   (should-exist "foo")))

(ert-deftest f-mkdir-test/multiple-levels-same-call ()
  (with-playground
   (f-mkdir "foo" "bar" "baz")
   (should-exist "foo/bar/baz")))

(ert-deftest f-mkdir-test/multiple-levels-different-calls ()
  (with-playground
   (f-mkdir "foo")
   (f-mkdir "foo" "bar")
   (f-mkdir "foo" "bar" "baz")
   (should-exist "foo/bar/baz")))


;;;; f-delete

(ert-deftest f-delete-test/file-in-directory ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.txt")
   (should-exist "foo/bar.txt")
   (f-delete "foo/bar.txt")
   (should-not-exist "foo/bar.txt")))

(ert-deftest f-delete-test/directory ()
  (with-playground
   (f-mkdir "foo")
   (should-exist "foo")
   (f-delete "foo")
   (should-not-exist "foo")))

(ert-deftest f-delete-test/directory-with-content ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.txt")
   (should-exist "foo/bar.txt")
   (f-delete "foo/bar.txt" t)
   (should-not-exist "foo/bar.txt")))

(ert-deftest f-delete-test/symlink-to-file ()
  (with-playground
   (f-touch "foo")
   (f-symlink "foo" "bar")
   (f-delete "bar")
   (should-exist "foo")
   (should-not-exist "bar")))

(ert-deftest f-delete-test/symlink-to-directory ()
  (with-playground
   (f-mkdir "foo")
   (f-symlink "foo" "bar")
   (f-delete "bar")
   (should-exist "foo")
   (should-not-exist "bar")))


;;;; f-symlink

(ert-deftest f-symlink-test/make-link-to-file ()
  (with-playground
   (f-touch "foo.txt")
   (f-symlink "foo.txt" "foo.link")
   (should (f-symlink? "foo.link"))))


;;;; f-move

(ert-deftest f-move-test/move-relative-path ()
  (with-playground
   (f-touch "foo.txt")
   (f-mkdir "bar")
   (f-move "foo.txt" "bar")
   (should-exist "bar/foo.txt")))

(ert-deftest f-move-test/move-absolute-path ()
  (with-playground
   (f-touch "foo.txt")
   (f-mkdir "bar")
   (f-move
    (f-expand "foo.txt" f-test/playground-path)
    (f-expand "bar" f-test/playground-path))
   (should-exist "bar/foo.txt")))

(ert-deftest f-move-test/rename-relative-path ()
  (with-playground
   (f-write "FOO" 'utf-8 "foo.txt")
   (f-move "foo.txt" "bar.txt")
   (should-exist "bar.txt" "FOO")))

(ert-deftest f-move-test/rename-absolute-path ()
  (with-playground
   (f-write "FOO" 'utf-8 "foo.txt")
   (f-move
    (f-expand "foo.txt" f-test/playground-path)
    (f-expand "bar.txt" f-test/playground-path))
   (should-exist "bar.txt" "FOO")))


;;;; f-copy

(ert-deftest f-copy-test/copy-relative-file ()
  (with-playground
   (f-write "FOO" 'utf-8 "foo.txt")
   (f-copy "foo.txt" "bar.txt")
   (should-exist "foo.txt" "FOO")
   (should-exist "bar.txt" "FOO")))

(ert-deftest f-copy-test/copy-absolute-file ()
  (with-playground
   (f-write "FOO" 'utf-8 "foo.txt")
   (f-copy
    (f-expand "foo.txt" f-test/playground-path)
    (f-expand "bar.txt" f-test/playground-path))
   (should-exist "foo.txt" "FOO")
   (should-exist "bar.txt" "FOO")))

(ert-deftest f-copy-test/copy-relative-dir-exists ()
  (with-playground
   (f-mkdir "foo")
   (f-mkdir "bar")
   (f-write "FILE" 'utf-8 "foo/file.txt")
   (f-copy "foo" "bar")
   (should-exist "foo/file.txt" "FILE")
   (should-exist "bar/foo/file.txt" "FILE")))

(ert-deftest f-copy-test/copy-relative-dir-does-not-exist ()
  (with-playground
   (f-mkdir "foo")
   (f-write "FILE" 'utf-8 "foo/file.txt")
   (f-copy "foo" "bar")
   (should-exist "foo/file.txt" "FILE")
   (should-exist "bar/file.txt" "FILE")))

(ert-deftest f-copy-test/copy-absolute-dir-exists ()
  (with-playground
   (f-mkdir "foo")
   (f-mkdir "bar")
   (f-write "FILE" 'utf-8 "foo/file.txt")
   (f-copy
    (f-expand "foo" f-test/playground-path)
    (f-expand "bar" f-test/playground-path))
   (should-exist "foo/file.txt" "FILE")
   (should-exist "bar/foo/file.txt" "FILE")))

(ert-deftest f-copy-test/copy-absolute-dir-does-not-exist ()
  (with-playground
   (f-mkdir "foo")
   (f-write "FILE" 'utf-8 "foo/file.txt")
   (f-copy
    (f-expand "foo" f-test/playground-path)
    (f-expand "bar" f-test/playground-path))
   (should-exist "foo/file.txt" "FILE")
   (should-exist "bar/file.txt" "FILE")))


;;;; f-touch

(ert-deftest f-touch-test/file-does-not-exist-relative-path ()
  (with-playground
   (should-not-exist "foo")
   (f-touch "foo")
   (should-exist "foo" "")))

(ert-deftest f-touch-test/file-does-not-exists-absolute-path ()
  (with-playground
   (let ((path (f-expand "foo" f-test/playground-path)))
     (f-touch path)
     (should-exist path ""))))

(ert-deftest f-touch-test/file-does-exist-text-file ()
  (with-playground
   (f-write "text" 'utf-8 "foo")
   (set-file-times "foo" '(12 34 0 0))
   (f-touch "foo")
   (should-exist "foo" "text")
   (should-not (equal (nth 5 (file-attributes "foo")) '(12 34 0 0)))))

(ert-deftest f-touch-file-test/does-exist-bytes-file ()
  (with-playground
   (f-write-bytes "data" "foo")
   (set-file-times "foo" '(12 34 0 0))
   (f-touch "foo")
   (should-exist "foo" "data")
   (should-not (equal (nth 5 (file-attributes "foo")) '(12 34 0 0)))))

(provide 'f-destructive-test)

;;; f-destructive-test.el ends here
