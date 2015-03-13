;;; f-predicates-test.el --- F: Predicate tests  -*- lexical-binding: t; -*-

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


;;;; f-exists?

(ert-deftest f-exists?-test/directory-does-exist ()
  (with-playground
   (f-mkdir "foo")
   (should (f-exists? "foo"))))

(ert-deftest f-exists?-test/file-does-exist ()
  (with-playground
   (f-touch "foo.txt")
   (should (f-exists? "foo.txt"))))

(ert-deftest f-exists?-test/does-not-exists ()
  (with-playground
   (should-not (f-exists? "foo.txt"))))


;;;; f-directory?/f-dir?

(ert-deftest f-directory?-test/is-directory ()
  (with-playground
   (f-mkdir "foo")
   (should (f-directory? "foo"))))

(ert-deftest f-directory?-test/is-file ()
  (with-playground
   (f-touch "foo.txt")
   (should-not (f-directory? "foo.txt"))))

(ert-deftest f-dir?-test/alias ()
  (with-playground
   (f-mkdir "foo")
   (should (f-dir? "foo"))))


;;;; f-file?

(ert-deftest f-file?-test/is-file ()
  (with-playground
   (f-touch "foo.txt")
   (should (f-file? "foo.txt"))))

(ert-deftest f-file?-test/is-directory ()
  (with-playground
   (f-mkdir "foo")
   (should-not (f-file? "foo"))))


;;;; f-symlink?

(ert-deftest f-symlink?-test/is-symlink ()
  (with-playground
   (f-touch "foo.txt")
   (f-symlink "foo.txt" "foo.link")
   (should (eq (f-symlink? "foo.link") t))))

(ert-deftest f-symlink?-test/is-not-symlink ()
  (with-playground
   (f-touch "foo.txt")
   (should (eq (f-symlink? "foo.txt") nil))))


;;;; f-readable?

(ert-deftest f-readable?-test/is-readable ()
  (with-playground
   (f-touch "foo.txt")
   (chmod "foo.txt" "400")
   (should (f-readable? "foo.txt"))))

(ert-deftest f-readable?-test/is-not-readable ()
  (with-playground
   (f-touch "foo.txt")
   (chmod "foo.txt" "000")
   (should-not (f-readable? "foo.txt"))))


;;;; f-writable?

(ert-deftest f-writeable?-test/is-readable ()
  (with-playground
   (f-touch "foo.txt")
   (chmod "foo.txt" "700")
   (should (f-writable? "foo.txt"))))

(ert-deftest f-writeable?-test/is-not-readable ()
  (with-playground
   (f-touch "foo.txt")
   (chmod "foo.txt" "400")
   (should-not (f-writable? "foo.txt"))))

(ert-deftest f-writeable?-test/is-readable ()
  (with-playground
   (f-touch "foo.txt")
   (chmod "foo.txt" "100")
   (should (f-executable? "foo.txt"))))

(ert-deftest f-writeable?-test/is-not-readable ()
  (with-playground
   (f-touch "foo.txt")
   (chmod "foo.txt" "200")
   (should-not (f-executable? "foo.txt"))))


;;;; f-absolute?

(ert-deftest f-absolute?-test/is-absolute ()
  (should (f-absolute? "/full/path/to/dir")))

(ert-deftest f-absolute?-test/is-relative ()
  (should-not (f-absolute? "path/to/dir")))


;;;; f-relative?

(ert-deftest f-relative?-test/is-relative ()
  (should (f-relative? "path/to/dir")))

(ert-deftest f-relative?-test/is-absolute ()
  (should-not (f-relative? "/full/path/to/dir")))


;;;; f-root?

(ert-deftest f-root?-test/is-root ()
  (should (f-root? "/")))

(ert-deftest f-root?-test/is-not-root ()
  (should-not (f-root? "/not/root")))

(ert-deftest f-root?-test/is-root-weird-syntax ()
  (should (f-root? "/bin/..")))


;;;; f-ext?

(ert-deftest f-ext?-test/ext-does-match ()
  (with-playground
   (f-touch "foo.el")
   (should (f-ext? "foo.el" "el"))))

(ert-deftest f-ext?-test/ext-does-not-match ()
  (with-playground
   (f-touch "foo.el")
   (should-not (f-ext? "foo.el" "txt"))))

(ert-deftest f-ext?-test/with-ext ()
  (with-playground
   (f-touch "foo.el")
   (should (f-ext? "foo.el"))))

(ert-deftest f-ext?-test/without-ext ()
  (with-playground
   (f-touch "foo")
   (should-not (f-ext? "foo"))))


;;;; f-same?/f-equal?

(ert-deftest f-same?/relative-equal ()
  (with-playground
   (should (f-same? "foo" "foo"))))

(ert-deftest f-same?/relative-not-equal ()
  (with-playground
   (should-not (f-same? "foo" "bar"))))

(ert-deftest f-same?/absolute-equal ()
  (with-playground
   (should (f-same? (f-expand "foo" f-test/playground-path)
                    (f-expand "foo" f-test/playground-path)))))

(ert-deftest f-same?/absolute-not-equal ()
  (with-playground
   (should-not (f-same? (f-expand "foo" f-test/playground-path)
                        (f-expand "bar" f-test/playground-path)))))

(ert-deftest f-same?/relative-and-absolute-equal ()
  (with-playground
   (should (f-same? "foo" (f-expand "foo" f-test/playground-path)))))

(ert-deftest f-same?/relative-and-absolute-not-equal ()
  (with-playground
   (should-not (f-same? "foo" (f-expand "bar" f-test/playground-path)))))

(ert-deftest f-same?/symlink ()
  (with-playground
   (f-touch "foo")
   (f-symlink "foo" "bar")
   (f-same? "foo" "bar")))

(ert-deftest f-equal?/alias ()
  (with-playground
   (should (f-equal? "foo" "foo"))))


;;;; f-parent-of?

(ert-deftest f-parent-of?-test/is-parent ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should (equal t (f-parent-of? "foo" "foo/bar")))
   (should (equal t (f-parent-of? "foo/bar" "foo/bar/baz")))
   (should (equal t (f-parent-of? "foo/bar/baz" "foo/bar/baz/qux")))))

(ert-deftest f-parent-of?-test/is-not-parent ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should-not (f-parent-of? "foo/bar" "foo"))
   (should-not (f-parent-of? "foo/bar/baz" "foo/bar"))
   (should-not (f-parent-of? "foo/bar/baz/qux" "foo/bar/baz"))))

(ert-deftest f-parent-of?-test/is-same ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should-not (f-parent-of? "foo" "foo"))
   (should-not (f-parent-of? "foo/bar" "foo/bar"))
   (should-not (f-parent-of? "foo/bar/baz" "foo/bar/baz"))
   (should-not (f-parent-of? "foo/bar/baz/qux" "foo/bar/baz/qux"))
   (should-not (f-parent-of? (f-root) (f-root)))))


;;;; f-child-of?

(ert-deftest f-child-of?-test/is-child ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should (equal t (f-child-of? "foo/bar" "foo")))
   (should (equal t (f-child-of? "foo/bar/baz" "foo/bar")))
   (should (equal t (f-child-of? "foo/bar/baz/qux" "foo/bar/baz")))))

(ert-deftest f-child-of?-test/is-not-child ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should-not (f-child-of? "foo" "foo/bar"))
   (should-not (f-child-of? "foo/bar" "foo/bar/baz"))
   (should-not (f-child-of? "foo/bar/baz" "foo/bar/baz/qux"))))

(ert-deftest f-child-of?-test/is-same ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should-not (f-child-of? "foo" "foo"))
   (should-not (f-child-of? "foo/bar" "foo/bar"))
   (should-not (f-child-of? "foo/bar/baz" "foo/bar/baz"))
   (should-not (f-child-of? "foo/bar/baz/qux" "foo/bar/baz/qux"))
   (should-not (f-child-of? (f-root) (f-root)))))


;;;; f-ancestor-of?

(ert-deftest f-ancestor-of?-test/is-ancestor ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should (equal t (f-ancestor-of? "foo" "foo/bar")))
   (should (equal t (f-ancestor-of? "foo" "foo/bar/baz")))
   (should (equal t (f-ancestor-of? "foo" "foo/bar/baz/qux")))
   (should (equal t (f-ancestor-of? "foo/bar" "foo/bar/baz")))
   (should (equal t (f-ancestor-of? "foo/bar" "foo/bar/baz/qux")))
   (should (equal t (f-ancestor-of? "foo/bar/baz" "foo/bar/baz/qux")))
   (should (equal t (f-ancestor-of? (f-root) (f-expand (car (f-directories (f-root))) (f-root)))))))

(ert-deftest f-ancestor-of?-test/is-not-ancestor ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should-not (f-ancestor-of? "foo/bar" "foo"))
   (should-not (f-ancestor-of? "foo/bar/baz" "foo"))
   (should-not (f-ancestor-of? "foo/bar/baz/qux" "foo"))
   (should-not (f-ancestor-of? "foo/bar/baz" "foo/bar"))
   (should-not (f-ancestor-of? "foo/bar/baz/qux" "foo/bar"))
   (should-not (f-ancestor-of? "foo/bar/baz/qux" "foo/bar/baz"))
   (should-not (f-ancestor-of? (f-expand (car (f-directories (f-root))) (f-root)) (f-root)))))

(ert-deftest f-ancestor-of?-test/is-same ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should-not (f-ancestor-of? "foo" "foo"))
   (should-not (f-ancestor-of? "foo/bar" "foo/bar"))
   (should-not (f-ancestor-of? "foo/bar/baz" "foo/bar/baz"))
   (should-not (f-ancestor-of? "foo/bar/baz/qux" "foo/bar/baz/qux"))
   (should-not (f-ancestor-of? (f-root) (f-root)))))


;;;; f-descendant-of?

(ert-deftest f-descendant-of?-test/is-descendant ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should (equal t (f-descendant-of? "foo/bar" "foo")))
   (should (equal t (f-descendant-of? "foo/bar/baz" "foo")))
   (should (equal t (f-descendant-of? "foo/bar/baz/qux" "foo")))
   (should (equal t (f-descendant-of? "foo/bar/baz" "foo/bar")))
   (should (equal t (f-descendant-of? "foo/bar/baz/qux" "foo/bar")))
   (should (equal t (f-descendant-of? "foo/bar/baz/qux" "foo/bar/baz")))
   (should (equal t (f-descendant-of? (f-expand (car (f-directories (f-root))) (f-root)) (f-root))))
   (should (equal t (f-descendant-of? "/foo/bar/baz/qux" "/foo/bar/baz")))))

(ert-deftest f-descendant-of?-test/is-not-descendant ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should-not (f-descendant-of? "foo" "foo/bar"))
   (should-not (f-descendant-of? "foo" "foo/bar/baz"))
   (should-not (f-descendant-of? "foo" "foo/bar/baz/qux"))
   (should-not (f-descendant-of? "foo/bar" "foo/bar/baz"))
   (should-not (f-descendant-of? "foo/bar" "foo/bar/baz/qux"))
   (should-not (f-descendant-of? "foo/bar/baz" "foo/bar/baz/qux"))
   (should-not (f-descendant-of? (f-root) (f-expand (car (f-directories (f-root))) (f-root))))
   (should-not (f-descendant-of? "/foo/bar/baz" "/foo/bar/baz/qux"))))

(ert-deftest f-descendant-of?-test/is-same ()
  (with-playground
   (f-mkdir "foo" "bar" "baz" "qux")
   (should-not (f-descendant-of? "foo" "foo"))
   (should-not (f-descendant-of? "foo/bar" "foo/bar"))
   (should-not (f-descendant-of? "foo/bar/baz" "foo/bar/baz"))
   (should-not (f-descendant-of? "foo/bar/baz/qux" "foo/bar/baz/qux"))
   (should-not (f-descendant-of? (f-root) (f-root)))))

(provide 'f-predicates-test)

;;; f-predicates-test.el ends here
