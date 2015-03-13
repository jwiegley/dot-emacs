;;; ht.el --- The missing hash table library for Emacs

;; Copyright (C) 2013 Wilfred Hughes

;; Author: Wilfred Hughes <me@wilfred.me.uk>
;; Version: 1.5
;; Keywords: hash table, hash map, hash

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

;; The missing hash table utility library for Emacs.
;;
;; See documentation on https://github.com/Wilfred/ht.el

;;; Code:

(eval-when-compile (require 'cl)) ;; dolist

(defmacro ht (&rest pairs)
  "Create a hash table with the key-value pairs given.
Keys are compared with `equal'.

\(fn (KEY-1 VALUE-1) (KEY-2 VALUE-2) ...)"
  (let* ((table-symbol (make-symbol "ht-temp"))
        (assignments
         (mapcar
          (lambda (pair) `(ht-set ,table-symbol ,@pair))
          pairs)))
    `(let ((,table-symbol (ht-create)))
       ,@assignments
       ,table-symbol)))

(defun ht-create (&optional test)
  "Create an empty hash table.

TEST indicates the function used to compare the hash
keys.  Default is `equal'.  It can be `eq', `eql', `equal' or a
user-supplied test created via `define-hash-table-test'."
  (make-hash-table :test (or test 'equal)))

(defun ht-from-alist (alist)
  "Create a hash table with initial values according to ALIST."
  (let ((h (ht-create)))
    ;; the first key-value pair in an alist gets precedence, so we
    ;; start from the end of the list:
    (dolist (pair (reverse alist) h)
      (let ((key (car pair))
            (value (cdr pair)))
        (ht-set h key value)))))

;; based on the excellent -partition from dash.el, but we aim to be self-contained
(defun ht/group-pairs (list)
  "Return a new list with the items in LIST grouped into pairs.
Errors if LIST doesn't contain an even number of elements."
  (let ((result)
        (sublist)
        (len 0))

    (while list
      ;; take the head of LIST and push onto SUBLIST
      (setq sublist (cons (car list) sublist))
      (setq list (cdr list))
      
      (setq len (1+ len))

      (when (= len 2)
        ;; push this two-item list onto RESULT
        (setq result (cons (nreverse sublist) result))
        (setq sublist nil)
        (setq len 0)))
    
    (when sublist (error "Expected an even number of elements"))
    (nreverse result)))

(defun ht-from-plist (plist)
  "Create a hash table with initial values according to PLIST."
  (let ((h (ht-create)))
    (dolist (pair (ht/group-pairs plist) h)
      (let ((key (car pair))
            (value (cadr pair)))
        (ht-set h key value)))))

(defun ht-get (table key &optional default)
  "Look up KEY in TABLE, and return the matching value.
If KEY isn't present, return DEFAULT (nil if not specified)."
  (gethash key table default))

(defun ht-set (table key value)
  "Associate KEY in TABLE with VALUE."
  (puthash key value table)
  nil)

(defun ht-update (table from-table)
  "Update TABLE according to every key-value pair in FROM-TABLE."
  (maphash
   (lambda (key value) (puthash key value table))
   from-table)
  nil)

(defun ht-merge (&rest tables)
  "Crete a new tables that includes all the key-value pairs from TABLES.
If multiple have tables have the same key, the key-value pair is used."
  (let ((merged (ht-create)))
    (mapc (lambda (table) (ht-update merged table)) tables)
    merged))

(defun ht-remove (table key)
  "Remove KEY from TABLE."
  (remhash key table))

(defun ht-clear (table)
  "Remove all keys from TABLE."
  (clrhash table)
  nil)

(defun ht-map (function table)
  "Apply FUNCTION to each key-value pair of TABLE, and make a list of the results.
FUNCTION is called with two arguments, KEY and VALUE."
  (let (results)
    (maphash
     (lambda (key value)
       (push (funcall function key value) results))
     table)
    results))

(defmacro ht-amap (form table)
  "Anaphoric version of `ht-map'.
For every key-value pair in TABLE, evaluate FORM with the
variables KEY and VALUE bound."
  `(ht-map (lambda (key value) ,form) ,table))

(defun ht-keys (table)
  "Return a list of all the keys in TABLE."
  (ht-amap key table))

(defun ht-values (table)
  "Return a list of all the values in TABLE."
  (ht-amap value table))

(defun ht-items (table)
  "Return a list of two-element lists '(key value) from TABLE."
  (ht-amap (list key value) table))

(defalias 'ht-each 'maphash
  "Apply FUNCTION to each key-value pair of TABLE.
Returns nil, used for side-effects only.")

(defmacro ht-aeach (form table)
  "Anaphoric version of `ht-each'.
For every key-value pair in TABLE, evaluate FORM with the
variables key and value bound."
  `(ht-each (lambda (key value) ,form) ,table))

(defun ht-to-plist (table)
  "Return a flat list '(key1 value1 key2 value2...) from TABLE.

Note that hash tables are unordered, so this cannot be an exact
inverse of `ht-from-plist'.  The following is not guaranteed:

\(let ((data '(a b c d)))
  (equalp data
          (ht-to-plist (ht-from-plist data))))"
  (apply 'append (ht-items table)))

(defun ht-copy (table)
  "Return a shallow copy of TABLE (keys and values are shared)."
  (copy-hash-table table))

(defun ht-to-alist (table)
  "Return a list of two-element lists '(key . value) from TABLE.

Note that hash tables are unordered, so this cannot be an exact
inverse of `ht-from-alist'.  The following is not guaranteed:

\(let ((data '((a . b) (c . d))))
  (equalp data
          (ht-to-alist (ht-from-alist data))))"
  (ht-amap (cons key value) table))

(defalias 'ht-p 'hash-table-p)

(defun ht-contains-p (table key)
  "Return 't if TABLE contains KEY."
  (not (eq (ht-get table key 'ht--not-found) 'ht--not-found)))

(provide 'ht)
;;; ht.el ends here
