;;; f-io-test.el --- F: IO related tests  -*- lexical-binding: t; -*-

;; Copyright (C) 2013 Sebastian Wiesner
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


;;;; f-write-bytes

(ert-deftest f-write-bytes-test/multibyte-string ()
  (with-playground
   (let ((err (should-error (f-write-bytes "☺ ☹" "foo.txt")
                            :type 'wrong-type-argument)))
     (should (equal (cdr err)
                    (list 'f-unibyte-string-p "☺ ☹"))))))

(ert-deftest f-write-bytes-test/unibyte-string ()
  (with-playground
   ;; Let's take some random bytes
   (let ((bytes (apply #'unibyte-string (-map #'random (-repeat 100 255)))))
     ;; Make a string of our bytes
     (f-write-bytes bytes "foo.txt")
     (should-exist "foo.txt" bytes))))


;;;; f-write/f-write-text

(ert-deftest f-write-text-test/unibyte-string ()
  (with-playground
   (f-write-text (unibyte-string 1 2 3 4 5) 'utf-8 "foo.txt")
   ;; Emacs only makes multibyte strings if actually required.
   (f-write-text "bar" 'utf-8 "bar.txt")
   (should-exist "bar.txt" "bar")))

(ert-deftest f-write-text-test/multibyte-string ()
  (with-playground
   (f-write-text "☺ ☹" 'utf-8 "foo.txt")
   (should-exist "foo.txt" (unibyte-string 226 152 186 32 226 152 185))
   (f-write-text "blök" 'iso-8859-1 "foo.txt")
   (should-exist "foo.txt" (unibyte-string 98 108 246 107))))

(ert-deftest f-write-test/alias ()
  (with-playground
   (f-write-text (unibyte-string 1 2 3 4 5) 'utf-8 "foo.txt")
   (f-write (unibyte-string 1 2 3 4 5) 'utf-8 "bar.txt")
   (should (equal (f-read "foo.txt") (f-read "bar.txt")))))


;;;; f-read-bytes

(ert-deftest f-read-bytes-test/ ()
  (with-playground
   (let ((bytes (apply #'unibyte-string (-map #'random (-repeat 100 255)))))
     (f-write-bytes bytes "foo.txt")
     (let ((content (f-read-bytes "foo.txt")))
       (should-not (multibyte-string-p content))
       (should (f-unibyte-string-p content))
       (should (string= content bytes))))))


;;;; f-read/f-read-text

(ert-deftest f-read-text-test/ ()
  (with-playground
   (f-write-bytes (unibyte-string 226 152 185 32 226 152 186) "foo.txt")
   (let ((text (f-read-text "foo.txt" 'utf-8)))
     (should (string= text "☹ ☺"))
     (should (multibyte-string-p text)))
   (f-write-bytes (unibyte-string 252 98 101 114) "foo.txt")
   (let ((text (f-read-text "foo.txt" 'iso-8859-1)))
     (should (string= text "über"))
     (should (multibyte-string-p text)))))

(ert-deftest f-read-text-test/no-coding-specified ()
  (with-playground
   (f-write-text "text" 'utf-8 "foo.txt")
   (should (equal (f-read-text "foo.txt") "text"))))

(ert-deftest f-read-test/alias ()
  (with-playground
   (f-write-bytes (unibyte-string 226 152 185 32 226 152 186) "foo.txt")
   (should (equal (f-read-text "foo.txt") (f-read "foo.txt")))))


;;;; f-append-text

(ert-deftest f-append-text/does-not-exist ()
  (with-playground
   (f-append-text "foo" 'utf-8 "foo.txt")
   (should-exist "foo.txt" "foo")))

(ert-deftest f-append-text/exists ()
  (with-playground
   (f-write "foo" 'utf-8 "foo.txt")
   (f-append-text "bar" 'utf-8 "foo.txt")
   (should-exist "foo.txt" "foobar")))

(ert-deftest f-append/alias ()
  (with-playground
   (f-append "foo" 'utf-8 "foo.txt")
   (should-exist "foo.txt" "foo")))


;;;; f-append-bytes

(ert-deftest f-append-bytes-test/does-not-exist ()
  (with-playground
   (let ((bytes (apply #'unibyte-string (-map #'random (-repeat 100 255)))))
     (f-append-bytes bytes "foo.txt")
     (should-exist "foo.txt" bytes))))

(ert-deftest f-append-bytes-test/exists ()
  (with-playground
   (let ((bytes (apply #'unibyte-string (-map #'random (-repeat 100 255)))))
     (f-write-bytes bytes "foo.txt")
     (f-append-bytes bytes "foo.txt")
     (should-exist "foo.txt" (concat bytes bytes)))))

(provide 'f-io-test)

;;; f-io-test.el ends here
