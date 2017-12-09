;;; simple-csv-parser-tests.el --- Tests for simple csv parser  -*- lexical-binding: t; -*-

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
(require 'simple-csv-parser)

(ert-deftest test-simple-csv ()
  (should
   (equal
    (s-parse-csv "a1s,b,d,e,f\na,,c,d,\n")
    '(("a1s" "b" "d" "e" "f")
      ("a" "" "c" "d" "")))))


(provide 'simple-csv-parser-tests)
;;; simple-csv-parser-tests.el ends here
