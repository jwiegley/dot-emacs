;;; full-csv-parser-tests.el --- Tests for full-csv-parser  -*- lexical-binding: t; -*-

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
(require 'full-csv-parser)

(ert-deftest test-full-csv ()
  (should
   (equal
    (parse-csv "\"a,1,s\",b,\r\nd,e,f")
    '(("a,1,s" "b" "")
      ("d" "e" "f"))))
  (should
   (equal
    (parse-csv "\"e\"\",f")
    (parsec-error-new-2 "\"" "`EOF'")))
  (should
   (equal
    (parse-csv "\"a,1,\r\n")
    (parsec-error-new-2 "\"" "`EOF'")))
  (should
   (equal
    (parse-csv "\"a,1,\",b,\r\nd,,f")
    '(("a,1," "b" "")
      ("d" "" "f")))))

(provide 'full-csv-parser-tests)
;;; full-csv-parser-tests.el ends here
