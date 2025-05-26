;;; loeb.el --- Loeb function in Emacs Lisp -*- lexical-binding: t; -*-

;; Copyright © 2025 John Wiegley <johnw@gnu.org>

;; Author: John Wiegley <johnw@gnu.org>
;; URL: https://github.com/jwiegley/dot-emacs
;; Keywords: function

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; This library provides the loeb function, for sequences (lists and vectors),
;; alists and plists.
;;
;; See https://github.com/quchen/articles/blob/master/loeb-moeb.md for more
;; details and motivation.

(require 'seq)
(require 'thunk)

(defun loeb-seq (fs)
  "The loeb function, implemented in Emacs Lisp.
Basically, you take a sequence of functions from a sequence to a
value, and calculate a sequence of values by passing the
\"final\" sequence to every one of those functions. But it's a
fixed point, so as long as it forms a DAG, the references all
work out.

Example:
  (loeb (list (lambda (xs) (length xs))
              (lambda (xs) (+ (thunk-force (nth 0 xs)) (length xs)))))
    ==> (2 4)"
  (letrec ((go (seq-map (lambda (f) (thunk-delay (funcall f go))) fs)))
    (seq-map #'thunk-force go)))

(defun loeb-alist (fs)
  "The loeb function, specialized to alists. See `loeb'.
Example:
  (loeb-alist '((foo . (lambda (alist)
                          (thunk-force (alist-get 'bar alist))))
                (bar . (lambda (alist) 2))))"
  (letrec ((go (seq-map
                (lambda (cell)
                  (cons (car cell)
                        (thunk-delay (funcall (cdr cell) go))))
                fs)))
    (seq-map (lambda (cell)
               (cons (car cell)
                     (thunk-force (cdr cell))))
             go)))

(defun loeb-plist-map! (fn plist)
  "Map FN over PLIST, modifying it in-place and returning it.
FN must take two arguments: the key and the value."
  (let ((plist-index plist))
    (while plist-index
      (let ((key (pop plist-index)))
        (setf (car plist-index) (funcall fn key (car plist-index))
              plist-index (cdr plist-index)))))
  plist)

(defun loeb-plist (fs)
  "The loeb function, specialized to plists. See `loeb'.
Example:
  (loeb-plist '(:foo (lambda (plist)
                        (thunk-force (plist-get plist :bar)))
                :bar (lambda (plist) 2)))"
  (letrec ((go (loeb-plist-map!
                (lambda (_key value)
                  (thunk-delay (funcall value go)))
                fs)))
    (loeb-plist-map! (lambda (_key value) (thunk-force value)) go)))

(defalias 'loeb-resolve 'thunk-delay)

(provide 'loeb)
