;;; pjson.el --- JSON parser using parsec.el         -*- lexical-binding: t; -*-

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

;; Ref: https://hackage.haskell.org/package/json-0.9.1/docs/src/Text-JSON-Parsec.html

;;; Code:

(defvar pjson-special-chars
  '((?\" . ?\")
    (?\\ . ?\\)
    (?/ . ?/)
    (?b . ?\b)
    (?f . ?\f)
    (?n . ?\n)
    (?r . ?\r)
    (?t . ?\t))
  "Characters which are escaped in JSON, with their elisp counterparts.")

(defsubst pjson-spaces ()
  (parsec-many-as-string
   (parsec-re "[[:space:]\r\n]")))

(defmacro pjson-tok (parser)
  `(parsec-return ,parser
     (pjson-spaces)))

(defun pjson-value ()
  (parsec-and
    (pjson-spaces)
    (pjson-jvaule)))

(defun pjson-jvalue ()
  (parsec-or (pjson-null)
             (pjson-boolean)
             (pjson-number)
             (pjson-string)
             (pjson-array)
             (pjson-object)))

(defsubst pjson-null ()
  (parsec-and
    (pjson-tok (parsec-str "null"))
    nil))

(defsubst pjson-boolean ()
  (parsec-or (parsec-and
               (pjson-tok (parsec-str "true"))
               t)
             (parsec-and
               (pjson-tok (parsec-str "false"))
               nil)))

(defsubst pjson-array ()
  (apply #'vector
         (parsec-between (pjson-tok (parsec-ch ?\[))
                         (pjson-tok (parsec-ch ?\]))
                         (parsec-sepby
                          (pjson-jvalue)
                          (pjson-tok (parsec-ch ?,))))))

(defun pjson-char ()
  (parsec-or
   (parsec-and (parsec-ch ?\\) (pjson-esc))
   (parsec-none-of ?\" ?\\)))

(defun pjson-esc ()
  (parsec-or
   (assoc-default
    (parsec-satisfy (lambda (x) (assq x pjson-special-chars)))
    pjson-special-chars)
   (parsec-and (parsec-ch ?u)
               (pjson-uni))))

(defun pjson-uni ()
  (format "%c" (string-to-number
                (parsec-re "[0-9a-zA-z]\\{4\\}")
                16)))

(defsubst pjson-string ()
  (parsec-between (pjson-tok (parsec-ch ?\"))
                  (pjson-tok (parsec-ch ?\"))
                  (parsec-many-as-string (pjson-char))))

(defun pjson-field ()
  (cons (parsec-return (pjson-string)
          (pjson-tok (parsec-ch ?:)))
        (pjson-jvalue)))

(defun pjson-object ()
  (parsec-between (pjson-tok (parsec-ch ?\{))
                  (pjson-tok (parsec-ch ?\}))
                  (parsec-sepby
                   (pjson-field)
                   (pjson-tok (parsec-ch ?,)))))

(defun pjson-number ()
  (pjson-tok (string-to-number
              (parsec-re "\\+?\\([0-9]+\\)\\(\\.[0-9]+\\)?\\([Ee][+-]?[0-9]+\\)?"))))

(defun pjson-parse (input)
  (parsec-with-input input
    (pjson-object)))

(provide 'pjson)
;;; pjson.el ends here
