;;; scheme-tests.el --- Tests for scheme parser      -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Free Software Foundation, Inc.

;; Author: Junpeng Qiu <qjpchmail@gmail.com>
;; Keywords:

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

;;

;;; Code:

(require 'ert)
(require 'scheme)

(ert-deftest test-scheme-number ()
  (should
   (equal (scheme-read "25")
          (scheme-number 25))))

(ert-deftest test-scheme-string ()
  (should
   (equal
    (scheme-read "\"This is a string\"")
    "This is a string")))

(ert-deftest test-scheme-list ()
  (should
   (equal
    (scheme-read "(symbol)")
    '(List
      (Atom . "symbol"))))
  (should
   (equal
    (scheme-read "(a test)")
    '(List
      (Atom . "a")
      (Atom . "test")))))

(ert-deftest test-scheme-dotted-list ()
  (should
   (equal
    (scheme-read "(a . test)")
    '(DottedList
      ((Atom . "a"))
      Atom . "test"))))

(ert-deftest test-scheme-nested ()
  (should
   (equal
    (scheme-read "(a (nested) test)")
    '(List
      (Atom . "a")
      (List
       (Atom . "nested"))
      (Atom . "test")))))

(ert-deftest test-scheme-quoted ()
  (should
   (equal
    (scheme-read "(a '(quoted (dotted . list)) test)")
    '(List
      (Atom . "a")
      (List
       (Atom . "quote")
       (List
        (Atom . "quoted")
        (DottedList
         ((Atom . "dotted"))
         Atom . "list")))
      (Atom . "test")))))

(provide 'scheme-tests)
;;; scheme-tests.el ends here
