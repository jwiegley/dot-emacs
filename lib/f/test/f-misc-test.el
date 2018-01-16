;;; f-misc-test.el --- F: Misc tests  -*- lexical-binding: t; -*-

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


;;;; f-glob

(ert-deftest f-glob-test/without-path ()
  (with-playground
   (f-touch "foo.el")
   (f-touch "baz.el")
   (f-mkdir "bar")
   (f-touch "bar/qux.el")
   (should
    (equal
     (mapcar 'f-filename (f-glob "*.el")) '("baz.el" "foo.el")))))

(ert-deftest f-glob-test/with-path ()
  (with-playground
   (f-touch "foo.el")
   (f-touch "baz.el")
   (f-mkdir "bar")
   (f-touch "bar/qux.el")
   (should
    (equal
     (mapcar 'f-filename (f-glob "*.el" "bar")) '("qux.el")))))


;;;; f-entries/f--entries

(ert-deftest f-entries-test/no-directories-or-files ()
  (with-playground
   (f-mkdir "foo")
   (should (equal (f-entries "foo") nil))))

(ert-deftest f-entries-test/with-files-and-directories ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.txt")
   (f-touch "foo/baz.txt")
   (f-mkdir "foo/qux")
   (should
    (equal
     (--map (f-relative it "foo") (f-entries "foo" nil t))
     '("qux" "baz.txt" "bar.txt")))))

(ert-deftest f-entries-test/with-callback-function ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.el")
   (f-touch "foo/baz.el")
   (f-touch "foo/qux.coffee")
   (let ((fn
          (lambda (entry)
            (equal (f-ext entry) "el"))))
     (should
      (equal
       (--map (f-relative it "foo") (f-entries "foo" fn t))
       '("baz.el" "bar.el"))))))

(ert-deftest f-entries-test/recursive ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.el")
   (f-mkdir "foo/bar")
   (f-touch "foo/bar/baz.el")
   (f-mkdir "foo/bar/qux")
   (f-touch "foo/bar/qux/hey.el")
   (should
    (equal
     (--map (f-relative it "foo") (f-entries "foo" nil t))
     '("bar.el" "bar" "bar/qux" "bar/baz.el" "bar/qux/hey.el")))))

(ert-deftest f-entries-test/anaphoric ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.el")
   (f-mkdir "foo/bar")
   (f-touch "foo/baz.el")
   (f-touch "foo/qux.coffee")
   (f-mkdir "foo/qux")
   (let* ((foo-path (f-expand "foo" f-test/playground-path))
          (el-files (-sort 'string< (--map (f-expand it foo-path) '("baz.el" "bar.el"))))
          (all-files (-sort 'string< (--map (f-expand it foo-path) '("baz.el" "bar.el" "qux.coffee" "bar" "qux")))))
     (should (equal (-sort 'string< (f--entries "foo" 'ignore)) all-files))
     (should (equal (-sort 'string< (f--entries "foo" (equal (f-ext it) "el") t)) el-files)))))


;;;; f-directories/f--directories

(ert-deftest f-directories-test/no-directories-or-files ()
  (with-playground
   (f-mkdir "foo")
   (should (equal (f-directories "foo") nil))))

(ert-deftest f-directories-test/with-files-and-directories ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.txt")
   (f-touch "foo/baz.txt")
   (f-mkdir "foo/qux")
   (should
    (equal
     (--map (f-relative it "foo") (f-directories "foo" nil t))
     '("qux")))))

(ert-deftest f-directories-test/with-callback-function ()
  (with-playground
   (f-mkdir "foo")
   (f-mkdir "foo/test")
   (f-mkdir "foo/baz")
   (f-mkdir "foo/baz/test")
   (f-touch "foo/test/baz.el")
   (f-touch "foo/baz/test/qux.el")
   (let ((fn
          (lambda (entry)
            (equal (f-filename entry) "test"))))
     (should
      (equal
       (--map (f-relative it "foo") (f-directories "foo" fn t))
       '("test" "baz/test"))))))

(ert-deftest f-directories-test/recursive ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.el")
   (f-mkdir "foo/bar")
   (f-touch "foo/bar/baz.el")
   (f-mkdir "foo/bar/qux")
   (f-touch "foo/bar/qux/hey.el")
   (should
    (equal
     (--map (f-relative it "foo") (f-directories "foo" nil t))
     '("bar" "bar/qux")))))

(ert-deftest f-directories-test/anaphoric ()
  (with-playground
   (f-mkdir "foo")
   (f-mkdir "foo/test")
   (f-mkdir "foo/baz")
   (f-mkdir "foo/baz/test")
   (f-touch "foo/test/baz.el")
   (f-touch "foo/baz/test/qux.el")
   (let* ((foo-path (f-expand "foo" f-test/playground-path))
          (test-dirs (-sort 'string< (--map (f-expand it foo-path) '("test" "baz/test"))))
          (all-dirs (-sort 'string< (--map (f-expand it foo-path) '("test" "baz" "baz/test")))))
     (should (equal (-sort 'string< (f--directories "foo" 'ignore :recursive)) all-dirs))
     (should (equal (-sort 'string< (f--directories "foo" (equal (f-filename it) "test") t)) test-dirs)))))


;;;; f-files/f--files

(ert-deftest f-files-test/no-files-or-files ()
  (with-playground
   (f-mkdir "foo")
   (should (equal (f-files "foo") nil))))

(ert-deftest f-files-test/with-files-and-files ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.txt")
   (f-touch "foo/baz.txt")
   (f-mkdir "foo/qux")
   (should
    (equal
     (--map (f-relative it "foo") (f-files "foo" nil t))
     '("baz.txt" "bar.txt")))))

(ert-deftest f-files-test/with-callback-function ()
  (with-playground
   (f-mkdir "foo")
   (f-mkdir "foo/test")
   (f-mkdir "foo/baz")
   (f-mkdir "foo/baz/test")
   (f-touch "foo/test/baz.el")
   (f-touch "foo/baz/test/qux.el")
   (let ((fn
          (lambda (entry)
            (equal (f-ext entry) "el"))))
     (should
      (equal
       (--map (f-relative it "foo") (f-files "foo" fn t))
       '("baz/test/qux.el" "test/baz.el"))))))

(ert-deftest f-files-test/recursive ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.el")
   (f-mkdir "foo/bar")
   (f-touch "foo/bar/baz.el")
   (f-mkdir "foo/bar/qux")
   (f-touch "foo/bar/qux/hey.el")
   (should
    (equal
     (--map (f-relative it "foo") (f-files "foo" nil t))
     '("bar.el" "bar/baz.el" "bar/qux/hey.el")))))

(ert-deftest f-files-test/anaphoric ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.el")
   (f-touch "foo/baz.el")
   (f-touch "foo/qux.coffee")
   (let* ((foo-path (f-expand "foo" f-test/playground-path))
          (el-files (-sort 'string< (--map (f-expand it foo-path) '("baz.el" "bar.el"))))
          (all-files (-sort 'string< (--map (f-expand it foo-path) '("baz.el" "bar.el" "qux.coffee")))))
     (should (equal (-sort 'string< (f--entries "foo" 'ignore)) all-files))
     (should (equal (-sort 'string< (f--entries "foo" (equal (f-ext it) "el") t)) el-files)))))

(ert-deftest f--files-test/with-files-and-files ()
  (with-playground
   (f-mkdir "foo")
   (f-touch "foo/bar.txt")
   (f-touch "foo/baz.txt")
   (f-mkdir "foo/qux")
   (should
    (equal
     (f--files "foo" 'identity t)
     (f-files "foo" nil t)))))



;;;; f-path-separator

(ert-deftest f-path-separator-test ()
  (unless (eq system-type 'windows-nt)
    (should (equal (f-path-separator) "/"))))


;;;; f-root

(ert-deftest f-root-test ()
  (should (equal (f-root) "/")))


;;;; f-traverse-upwards/f--traverse-upwards

(ert-deftest f-traverse-upwards-test/no-start-path-specified ()
  (with-playground
   (f-touch "foo")
   (f-mkdir "bar" "baz")
   (f-touch (f-join "bar" "baz" "qux"))
   (let ((default-directory (f-join f-test/playground-path "bar" "baz" "qux")))
     (should
      (equal
       f-test/playground-path
       (f-traverse-upwards
        (lambda (path)
          (f-file? (f-expand "foo" path)))))))))

(ert-deftest f-traverse-upwards-test/specified-path-is-file ()
  (with-playground
   (f-touch "foo")
   (f-mkdir "bar" "baz")
   (f-touch (f-join "bar" "baz" "qux"))
   (should
    (equal
     f-test/playground-path
     (f-traverse-upwards
      (lambda (path)
        (f-file? (f-expand "foo" path)))
      (f-join "bar" "baz" "qux"))))))

(ert-deftest f-traverse-upwards-test/specified-path-is-directory ()
  (with-playground
   (f-touch "foo")
   (f-mkdir "bar" "baz")
   (should
    (equal
     f-test/playground-path
     (f-traverse-upwards
      (lambda (path)
        (f-file? (f-expand "foo" path)))
      (f-join f-test/playground-path "bar" "baz"))))))

(ert-deftest f-traverse-upwards-test/specified-path-is-relative ()
  (with-playground
   (f-touch "foo")
   (f-mkdir "bar" "baz")
   (should
    (equal
     f-test/playground-path
     (f-traverse-upwards
      (lambda (path)
        (f-file? (f-expand "foo" path)))
      (f-join "bar" "baz"))))))

(ert-deftest f-traverse-upwards-test/specified-path-matches-fn ()
  (with-playground
   (f-touch "foo")
   (f-mkdir "bar" "baz")
   (should
    (equal
     (f-join f-test/playground-path "bar" "baz")
     (f-traverse-upwards
      (lambda (path)
        (equal (f-filename path) "baz"))
      (f-join f-test/playground-path "bar" "baz"))))))

(ert-deftest f-traverse-upwards-test/searching-for-root ()
  (should (f-root? (f-traverse-upwards 'f-root?))))

(ert-deftest f-traverse-upwards-test/no-path-in-traversal-matches ()
  (with-playground
   (f-touch "foo")
   (f-mkdir "bar" "baz")
   (should-not
    (f-traverse-upwards
     (lambda (path)
       (equal (f-filename path) "qux"))
     (f-join f-test/playground-path "bar" "baz")))))

(ert-deftest f--traverse-upwards-test ()
  (with-playground
   (f-touch "foo")
   (f-mkdir "bar" "baz")
   (should
    (equal
     f-test/playground-path
     (f--traverse-upwards
      (f-file? (f-expand "foo" it))
      (f-join f-test/playground-path "bar" "baz"))))))

(provide 'f-misc-test)

;;; f-misc-test.el ends here
