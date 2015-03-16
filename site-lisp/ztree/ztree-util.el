;;; ztree-util.el --- Auxulary utilities for the ztree package

;; Copyright (C) 2013 Alexey Veretennikov
;;
;; Author: Alexey Veretennikov <alexey dot veretennikov at gmail dot com>
;; Created: 2013-11-1l
;; Version: 1.0.0
;; Keywords: files
;; URL: https://github.com/fourier/ztree
;; Compatibility: GNU Emacs GNU Emacs 24.x
;;
;; This file is NOT part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;;; Commentary:

;;; Code:
(defun ztree-find (where which)
  "find element of the list `where` matching predicate `which`"
  (catch 'found
    (dolist (elt where)
      (when (funcall which elt)
        (throw 'found elt)))
    nil))

(defun ztree-filter (condp lst)
  "Filter out elements of the list `lst` not satisfying predicate `condp`.
Taken from http://www.emacswiki.org/emacs/ElispCookbook#toc39"
  (delq nil
        (mapcar (lambda (x) (and (funcall condp x) x)) lst)))


(defun printable-string (string)
  "Strip newline character from file names, like 'Icon\n'"
  (replace-regexp-in-string "\n" "" string))  

(defun file-short-name (file)
  "Base file/directory name. Taken from
 http://lists.gnu.org/archive/html/emacs-devel/2011-01/msg01238.html"
  (printable-string (file-name-nondirectory (directory-file-name file))))


(defun newline-and-begin ()
  (newline)
  (beginning-of-line))

(defun car-atom (value)
  "Returns value if value is an atom, otherwise (car value) or nil.
Used since car-safe returns nil for atoms"
  (if (atom value) value (car value)))


(defun insert-with-face (text face)
  "Insert text with the face provided"
  (let ((start (point)))
    (insert text)
    (put-text-property start (point) 'face face)))


(defmacro defrecord (record-name record-fields)
  "Create a record (structure) and getters/setters.

Record is the following set of functions:
 - Record constructor with name \"record-name\"-create and list of
arguments which will be assigned to record-fields
 - Record getters with names \"record-name\"-\"field\" accepting one
argument - the record; \"field\" is from \"record-fields\" symbols
 - Record setters with names \"record-name\"-set-\"field\" accepting two
arguments - the record and the field value

Example:
\(defrecord person (name age))

will be expanded to the following functions:

\(defun person-create (name age) (...)
\(defun person-name (record) (...)
\(defun person-age (record) (...)
\(defun person-set-name (record value) (...)
\(defun person-set-age (record value) (...)"
  (let ((ctor-name (intern (concat (symbol-name record-name) "-create")))
        (rec-var (make-symbol "record")))
    `(progn
       ;; constructor with the name "record-name-create"
       ;; with arguments list "record-fields" expanded
       (defun ,ctor-name (,@record-fields)
         (let ((,rec-var))
           ,@(mapcar #'(lambda (x) 
                      (list 'setq rec-var (list 'plist-put rec-var (list 'quote x) x)))
                    record-fields)))
       ;; getters with names "record-name-field" where the "field"
       ;; is from record-fields
       ,@(mapcar #'(lambda (x)
                    (let ((getter-name (intern (concat (symbol-name record-name)
                                                       "-"
                                                       (symbol-name x)))))
                      `(progn
                         (defun ,getter-name (,rec-var)
                           (plist-get ,rec-var ',x)
                           ))))
                record-fields)
       ;; setters wit names "record-name-set-field where the "field"
       ;; is from record-fields
       ;; arguments for setters: (record value)
       ,@(mapcar #'(lambda (x)
                     (let ((setter-name (intern (concat (symbol-name record-name)
                                                        "-set-"
                                                        (symbol-name x)))))
                       `(progn
                          (defun ,setter-name (,rec-var value)
                            (setq ,rec-var (plist-put ,rec-var ',x value))
                            ))))
                 record-fields))))


(provide 'ztree-util)

;;; ztree-util.el ends here
