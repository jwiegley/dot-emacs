;;; url-str-parser-tests.el --- Tests for url-str-parser  -*- lexical-binding: t; -*-

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
(require 'url-str-parser)

(ert-deftest test-url-str ()
  (should
   (equal
    (url-str-parse "foo=bar&a%21=b+c")
    '(("foo" Just . "bar")
      ("a!" Just . "b c"))))
  (should
   (equal
    (url-str-parse "foo=&a%21=b+c")
    '(("foo" Just . "")
      ("a!" Just . "b c"))))
  (should
   (equal
    (url-str-parse "foo&a%21=b+c")
    '(("foo" . Nothing)
      ("a!" Just . "b c")))))

(provide 'url-str-parser-tests)
;;; url-str-parser-tests.el ends here
