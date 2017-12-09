;;; scheme.el --- Scheme parser using parsec.el      -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Free Software Foundation, Inc.

;; Author: Junpeng Qiu <qjpchmail@gmail.com>
;; Keywords: extensions

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

;; Ref: https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours/

;;; Code:

(defsubst scheme-bool (value)
  (cons 'Bool value))

(defsubst scheme-true ()
  (scheme-bool 'True))

(defsubst scheme-false ()
  (scheme-bool 'False))

(defsubst scheme-atom (atom)
  (cons 'Atom atom))

(defsubst scheme-number (number)
  (cons 'Number number))

(defsubst scheme-list (&rest values)
  (cons 'List values))

(defsubst scheme-dotted-list (head tail)
  (cons 'DottedList (cons head tail)))

(defsubst scheme-symbol ()
  (parsec-re "[$!#%&|*+/:<=>?@^_~-]"))

(defsubst scheme-spaces ()
  (parsec-many (parsec-ch ? )))

(defun scheme-parse-string ()
  (parsec-and (parsec-ch ?\")
              (parsec-return (parsec-many-as-string (parsec-none-of ?\"))
                (parsec-ch ?\"))))

(defun scheme-parse-atom ()
  (let (first rest atom)
    (parsec-and (setq first (parsec-or (parsec-letter) (scheme-symbol)))
                (setq rest (parsec-many (parsec-or (parsec-letter)
                                                   (parsec-digit)
                                                   (scheme-symbol)))))
    (setq atom (parsec-list-to-string (cons first rest)))
    (cond
     ((string= atom "#t") (scheme-true))
     ((string= atom "#f") (scheme-false))
     (t (scheme-atom atom)))))

(defun scheme-parse-number ()
  (scheme-number
   (string-to-number (parsec-many1-as-string (parsec-digit)))))

(defun scheme-parse-list ()
  (apply #'scheme-list (parsec-sepby (scheme-parse-expr) (scheme-spaces))))

(defun scheme-parse-dotted-list ()
  (scheme-dotted-list (parsec-endby (scheme-parse-expr) (scheme-spaces))
                      (parsec-and
                        (parsec-ch ?.)
                        (scheme-spaces)
                        (scheme-parse-expr))))

(defun scheme-parse-quoted ()
  (parsec-and
    (parsec-ch ?\')
    (scheme-list (scheme-atom "quote") (scheme-parse-expr))))

(defun scheme-parse-expr ()
  (parsec-or (scheme-parse-atom)
             (scheme-parse-string)
             (scheme-parse-number)
             (scheme-parse-quoted)
             (parsec-between
              (parsec-ch ?\()
              (parsec-ch ?\))
              (parsec-or
               (parsec-try
                (scheme-parse-list))
               (scheme-parse-dotted-list)))))

(defun scheme-read (expr)
  (parsec-with-input expr
    (scheme-parse-expr)))

(provide 'scheme)
;;; scheme.el ends here
