;;; pjson-tests.el --- Test for parsec json parser   -*- lexical-binding: t; -*-

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
(require 'pjson)

(ert-deftest test-pjson-number ()
  (should
   (equal
    (parsec-with-input "123"
      (pjson-number))
    123)))

(ert-deftest test-pjson-boolean ()
  (should
   (equal
    (parsec-with-input "false"
      (pjson-boolean))
    nil)))

(ert-deftest test-pjson-null ()
  (should
   (equal
    (parsec-with-input "null"
      (pjson-null))
    nil)))

(ert-deftest test-pjson-array ()
  (should
   (equal
    (parsec-with-input "[1,true,1,\"abc\",[1],null)"
      (pjson-array))
    (parsec-error-new-2 "]" ")")))
  (should
   (equal
    (parsec-with-input "[1,true,1,\"abc\",[1],null]"
      (pjson-array))
    (vector 1 t 1 "abc"
            (vector 1)
            nil))))
(ert-deftest test-pjson-string ()
  (should
   (equal
    (parsec-with-input "\"asdf\""
      (pjson-string))
    "asdf")))

(ert-deftest test-pjson-object ()
  (should
   (equal
    (parsec-with-input "{\"a\" :1, \"b\":2, \"c\":[1,true] }"
      (pjson-object))
    '(("a" . 1)
      ("b" . 2)
      ("c" .
       [1 t])))))

(ert-deftest test-pjson-jvalue ()
  (should
   (equal
    (parsec-with-input "[false]" (pjson-jvalue))
    (vector nil))))

(ert-deftest test-pjson-parse ()
  (should
   (equal
    (pjson-parse "{\"a\" :1, \"b\":2, \"c\":[1,{\"d\":null}]}")
    '(("a" . 1)
      ("b" . 2)
      ("c" .
       [1
        (("d"))]))))
  (should
   (equal
    (pjson-parse  "{\"a\" :1, \"b\":2, [{ \"c\":[1,true] }]}")
    (parsec-error-new-2 "\"" "["))))

(provide 'pjson-tests)
;;; pjson-tests.el ends here
