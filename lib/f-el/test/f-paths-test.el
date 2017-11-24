;;; f-paths-test.el --- F: Path related tests  -*- lexical-binding: t; -*-

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


;;;; f-join

(ert-deftest f-join-test/single-path-relative ()
  (should (equal (f-join "path") "path")))

(ert-deftest f-join-test/single-path-absolute ()
  (should (equal (f-join "/path") "/path")))

(ert-deftest f-join-test/multiple-paths-relative ()
  (should (equal (f-join "path" "to" "file") "path/to/file")))

(ert-deftest f-join-test/multiple-paths-absolute ()
  (should (equal (f-join "/path" "to" "file") "/path/to/file"))
  (should (equal (f-join "/" "path" "to" "file") "/path/to/file")))

(ert-deftest f-join-test/root ()
  (should (equal (f-join "/") "/")))


;;;; f-split

(ert-deftest f-split-test/single-path-relative ()
  (should (equal (f-split "path") '("path"))))

(ert-deftest f-split-test/single-path-absolute ()
  (should (equal (f-split "/path") '("/" "path"))))

(ert-deftest f-split-test/multiple-paths-relative ()
  (should (equal (f-split "path/to/file") '("path" "to" "file"))))

(ert-deftest f-split-test/multiple-paths-absolute ()
  (should (equal (f-split "/path/to/file") '("/" "path" "to" "file"))))

(ert-deftest f-split-test/inverse-of-join ()
  (should (equal (f-split (apply 'f-join (f-split "/path/to/file")))
                 '("/" "path" "to" "file"))))

(ert-deftest f-split-test/root ()
  (should (equal (f-split "/") '("/"))))


;;;; f-expand

(ert-deftest f-expand-test/no-dir ()
  (with-default-directory
   (should (equal (f-expand "foo") "/default/directory/foo"))))

(ert-deftest f-expand-test/with-dir ()
  (with-default-directory
   (should (equal (f-expand "foo" "/other") "/other/foo"))))

(ert-deftest f-expand-test/skip-handlers ()
  ;; If handlers are used, Tramp will try to connect but fail with an
  ;; exception, hence this will fail.
  (f-expand "foo:" "/"))


;;;; f-filename

(ert-deftest f-filename-test/relative ()
  (should (equal (f-filename "path/to/file") "file")))

(ert-deftest f-filename-test/absolute ()
  (should (equal (f-filename "/path/to/file") "file")))

(ert-deftest f-filename-test/with-extension ()
  (should (equal (f-filename "/path/to/file.txt") "file.txt")))

(ert-deftest f-filename-test/with-ending-slash ()
  (should (equal (f-filename "/path/to/dir/") "dir")))


;;;; f-dirname

(ert-deftest f-dirname-test/directory-relative ()
  (with-playground
   (f-mkdir "foo" "bar" "baz")
   (should (equal (f-dirname "foo/bar/baz") "foo/bar/"))))

(ert-deftest f-dirname-test/file-relative ()
  (with-playground
   (f-mkdir "foo" "bar" "baz")
   (f-touch "foo/bar/baz/qux.txt")
   (should (equal (f-dirname "foo/bar/baz/qux.txt") "foo/bar/baz/"))))

(ert-deftest f-dirname-test/directory-absolute ()
  (with-playground
   (f-mkdir "foo" "bar" "baz")
   (should
    (equal
     (f-dirname (f-expand "foo/bar/baz" f-test/playground-path))
     (f-expand "foo/bar/" f-test/playground-path)))))

(ert-deftest f-dirname-test/file-absolute ()
  (with-playground
   (f-mkdir "foo" "bar" "baz")
   (f-touch "foo/bar/baz/qux.txt")
   (should
    (equal
     (f-dirname (f-expand "foo/bar/baz/qux.txt" f-test/playground-path))
     (f-expand "foo/bar/baz/" f-test/playground-path)))))

(ert-deftest f-dirname-test/file-with-ending-slash ()
  (with-playground
   (f-mkdir "foo" "bar" "baz")
   (should
    (equal
     (f-dirname "foo/bar/baz/") "foo/bar/"))))

(ert-deftest f-dirname-test/parent-alias ()
  (with-playground
   (f-mkdir "foo" "bar" "baz")
   (should (equal (f-parent "foo/bar/baz") "foo/bar/"))))

(ert-deftest f-dirname-test/root ()
  (with-playground
   (should-not (f-parent (f-root)))))


;;;; f-common-parent
(ert-deftest f-common-parent/directory-relative ()
  (should (equal (f-common-parent '("foo/bar/baz" "foo/bar/qux" "foo/bar/mux")) "foo/bar/"))
  (should (equal (f-common-parent '("foo/bar/baz" "foo/bar/qux" "foo/bax/mux")) "foo/")))

(ert-deftest f-common-parent/directory-absolute ()
  (should (equal (f-common-parent '("/foo/bar/baz" "/foo/bar/qux" "/foo/bar/mux")) "/foo/bar/"))
  (should (equal (f-common-parent '("/foo/bar/baz" "/foo/bar/qux" "/foo/bax/mux")) "/foo/")))

(ert-deftest f-common-parent/no-common-parent ()
  (should (equal (f-common-parent '("foo/bar/baz" "foo/bar/qux" "fo/bar/mux")) "")))

(ert-deftest f-common-parent/root-common-parent ()
  (should (equal (f-common-parent '("/foo" "/bar")) "/")))

(ert-deftest f-common-parent/single-file ()
  (should (equal (f-common-parent '("foo/bar/baz")) "foo/bar/"))
  (should (equal (f-common-parent '("baz")) "./")))

(ert-deftest f-common-parent/same-path ()
  (should (equal (f-common-parent '("foo/bar/baz" "foo/bar/baz")) "foo/bar/baz/"))
  (should (equal (f-common-parent '("foo" "foo")) "foo/")))

(ert-deftest f-common-parent/empty-list ()
  (should (equal (f-common-parent nil) nil)))


;;;; f-ext

(ert-deftest f-ext-test/no-extension ()
  (should (equal (f-ext "path/to/file") nil)))

(ert-deftest f-ext-test/single-extension ()
  (should (equal (f-ext "path/to/file.txt") "txt")))

(ert-deftest f-ext-test/multiple-extensions ()
  (should (equal (f-ext "path/to/file.txt.org") "org")))


;;;; f-no-ext

(ert-deftest f-no-ext-test/no-extension ()
  (should (equal (f-no-ext "path/to/file") "path/to/file")))

(ert-deftest f-no-ext-test/single-extension ()
  (should (equal (f-no-ext "path/to/file.txt") "path/to/file")))

(ert-deftest f-no-ext-test/multiple-extensions ()
  (should (equal (f-no-ext "path/to/file.txt.org") "path/to/file.txt")))


;;;; f-swap-ext

(ert-deftest f-swap-ext-test/no-extension ()
  (should-error (f-swap-ext "path/to/file.txt" "")))

(ert-deftest f-swap-ext-test/with-extension ()
  (should (equal (f-swap-ext "path/to/file.txt" "org")
                 "path/to/file.org")))


;;;; f-base

(ert-deftest f-base-test/no-extension ()
  (should (equal (f-base "path/to/file") "file")))

(ert-deftest f-base-test/single-extension ()
  (should (equal (f-base "path/to/file.txt") "file")))

(ert-deftest f-base-test/multiple-extensions ()
  (should (equal (f-base "path/to/file.txt.org") "file.txt")))


;;;; f-relative

(ert-deftest f-relative-test/with-path ()
  (should (equal (f-relative "/some/path/relative/to/my/file.txt" "/some/path/") "relative/to/my/file.txt")))

(ert-deftest f-relative-test/without-path ()
  (with-default-directory
   (should (equal (f-relative "/default/directory/my/file.txt") "my/file.txt"))))


;;;; f-short

(ert-deftest f-short-test/home ()
  (let ((home (getenv "HOME")))
    (should (equal (f-short (f-expand "Code/bar" home)) "~/Code/bar"))))

(ert-deftest f-short-test/other ()
  (should (equal (f-short "/path/to/Code/bar") "/path/to/Code/bar")))

(ert-deftest f-short-test/alias ()
  (let ((home (getenv "HOME")))
    (should (equal (f-abbrev (f-expand "Code/bar" home)) "~/Code/bar")))
  (should (equal (f-abbrev "/path/to/Code/bar") "/path/to/Code/bar")))


;;;; f-long

(ert-deftest f-long-test/home ()
  (let ((home (getenv "HOME")))
    (should (equal (f-long "~/Code/bar") (f-expand "Code/bar" home)))))

(ert-deftest f-long-test/other ()
  (should (equal (f-long "/path/to/Code/bar") "/path/to/Code/bar")))


;;;; f-cannonical

(ert-deftest f-canonical-test/path ()
  (should (equal (f-canonical f-test/playground-path) f-test/playground-path)))

(ert-deftest f-canonical-test/symlink ()
  (with-playground
   (f-touch "foo")
   (f-symlink "foo" "bar")
   (should
    (equal
     (f-expand "foo" f-test/playground-path)
     (f-canonical (f-expand "bar" f-test/playground-path))))))


;;;; f-slash

(ert-deftest f-slash-test/absolute-no-slash ()
  (with-playground
   (f-mkdir "foo")
   (let ((foo (f-expand "foo" f-test/playground-path)))
     (should (equal (f-slash foo) (concat foo "/"))))))

(ert-deftest f-slash-test/absolute-with-slash ()
  (with-playground
   (f-mkdir "foo")
   (let ((foo (f-expand "foo" f-test/playground-path)))
     (should (equal (f-slash (concat foo "/")) (concat foo "/"))))))

(ert-deftest f-slash-test/relative-no-slash ()
  (with-playground
   (f-mkdir "foo")
   (should (equal (f-slash "foo") "foo/"))))

(ert-deftest f-slash-test/relative-with-slash ()
  (with-playground
   (f-mkdir "foo")
   (should (equal (f-slash "foo/") "foo/"))))

(ert-deftest f-slash-test/relative-file ()
  (with-playground
   (f-touch "foo")
   (should (equal (f-slash "foo") "foo"))))

(ert-deftest f-slash-test/absolute-file ()
  (with-playground
   (f-touch "foo")
   (let ((foo (f-expand "foo" f-test/playground-path)))
     (should (equal (f-slash foo) foo)))))

(ert-deftest f-slash-test/symlink-to-file ()
  (with-playground
   (f-touch "foo")
   (f-symlink "foo" "bar")
   (let ((bar (f-expand "bar" f-test/playground-path)))
     (should (equal (f-slash bar) bar)))))

(ert-deftest f-slash-test/symlink-to-directory ()
  (with-playground
   (f-mkdir "foo")
   (f-symlink "foo" "bar")
   (let ((bar (f-expand "bar" f-test/playground-path)))
     (should (equal (f-slash bar) (concat bar "/"))))))

(ert-deftest f-slash-test/non-existing-file-or-directory ()
  (with-playground
   (let ((foo (f-expand "foo" f-test/playground-path)))
     (should (equal (f-slash foo) foo)))))


;;;; f-full

(ert-deftest f-full-test/relative-no-slash ()
  (with-playground
   (f-mkdir "foo")
   (should (equal (f-full "foo") (concat (f-expand "foo" f-test/playground-path) "/")))))

(ert-deftest f-full-test/relative-with-slash ()
  (with-playground
   (f-mkdir "foo")
   (should (equal (f-full "foo/") (concat (f-expand "foo" f-test/playground-path) "/")))))

(ert-deftest f-full-test/relative-tilde ()
  (with-playground
   (f-mkdir "foo")
   (should (equal (f-full (f-short (f-expand "foo" f-test/playground-path)))
                  (concat (f-expand "foo" f-test/playground-path) "/")))))

(ert-deftest f-full-test/absolute-no-slash ()
  (with-playground
   (f-mkdir "foo")
   (let ((foo (f-expand "foo" f-test/playground-path)))
     (should (equal (f-full foo) (concat foo "/"))))))

(ert-deftest f-full-test/absolute-with-slash ()
  (with-playground
   (f-mkdir "foo")
   (let ((foo (f-expand "foo" f-test/playground-path)))
     (should (equal (f-full (concat foo "/")) (concat foo "/"))))))

(ert-deftest f-full-test/absolute-tilde ()
  (with-playground
   (f-mkdir "foo")
   (let ((foo (f-expand "foo" f-test/playground-path)))
     (should (equal (f-full (f-short foo)) (concat foo "/"))))))

(ert-deftest f-full-test/file ()
  (with-playground
   (f-touch "foo")
   (should (equal (f-full "foo") (f-expand "foo" f-test/playground-path)))))

(ert-deftest f-full-test/file-tilde ()
  (with-playground
   (f-touch "foo")
   (should (equal (f-full (f-short "foo")) (f-expand "foo" f-test/playground-path)))))

;;;; f-uniquify

(ert-deftest f-uniquify/no-conflict ()
  (should (equal (f-uniquify '("/foo/bar" "/foo/baz" "/foo/quux")) '("bar" "baz" "quux"))))

(ert-deftest f-uniquify/single-conflict ()
  (should (equal (f-uniquify '("/foo/bar" "/www/bar" "/foo/quux")) '("foo/bar" "www/bar" "quux"))))

(ert-deftest f-uniquify/single-conflict-shared-subpath ()
  (should (equal (f-uniquify '("/foo/bar" "/www/bar" "/www/bar/quux")) '("foo/bar" "www/bar" "quux"))))

(ert-deftest f-uniquify/recursive-conflict ()
  (should (equal (f-uniquify '("/foo/bar" "/foo/baz" "/home/www/bar" "/home/www/baz" "/var/foo" "/opt/foo/www/baz"))
                 '("foo/bar" "www/bar" "foo/baz" "home/www/baz" "foo/www/baz" "foo"))))

;;;; f-uniquify-alist

(ert-deftest f-uniquify/no-conflict ()
  (should (equal (f-uniquify-alist '("/foo/bar" "/foo/baz" "/foo/quux")) '(("/foo/bar" . "bar") ("/foo/baz" . "baz") ("/foo/quux" . "quux")) )))

(ert-deftest f-uniquify-alist/single-conflict ()
  (should (equal (f-uniquify-alist '("/foo/bar" "/www/bar" "/foo/quux")) '(("/foo/bar" . "foo/bar") ("/www/bar" . "www/bar") ("/foo/quux" . "quux")) )))

(ert-deftest f-uniquify-alist/single-conflict-shared-subpath ()
  (should (equal (f-uniquify-alist '("/foo/bar" "/www/bar" "/www/bar/quux")) '(("/foo/bar" . "foo/bar") ("/www/bar" . "www/bar") ("/www/bar/quux" . "quux")))))

(ert-deftest f-uniquify-alist/recursive-conflict ()
  (should (equal (f-uniquify-alist '("/foo/bar" "/foo/baz" "/home/www/bar" "/home/www/baz" "/var/foo" "/opt/foo/www/baz"))
                 '(("/foo/bar" . "foo/bar") ("/home/www/bar" . "www/bar") ("/foo/baz" . "foo/baz") ("/home/www/baz" . "home/www/baz") ("/opt/foo/www/baz" . "foo/www/baz") ("/var/foo" . "foo")) )))

(provide 'f-paths-test)

;;; f-paths-test.el ends here
