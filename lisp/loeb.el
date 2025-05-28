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

(defun loeb-seq* (fs)
  "The loeb function, implemented in Emacs Lisp.
This version does not force all values before returning.
See `loeb-seq' for more information."
  (letrec ((go (seq-map (lambda (f) (thunk-delay (funcall f go))) fs)))
    go))

(defun loeb-seq (fs)
  "The loeb function, implemented in Emacs Lisp.
Basically, you take a sequence of functions from a sequence to a
value, and calculate a sequence of values by passing the
\"final\" sequence to every one of those functions. But it's a
fixed point, so as long as it forms a DAG, the references all
work out.

Example:
  (loeb-seq (list (lambda (xs) (length xs))
                  (lambda (xs) (+ (loeb-resolve (nth 0 xs)) (length xs)))))
    ==> (2 4)"
  (seq-map #'thunk-force (loeb-seq* fs)))

(defun loeb-alist* (fs)
  "The loeb function, specialized to alists. See `loeb'.
This version does not force all values before returning.
See `loeb-alist' for more information."
  (letrec ((go (seq-map
                (lambda (cell)
                  (cons (car cell)
                        (thunk-delay (funcall (cdr cell) go))))
                fs)))
    go))

(defun loeb-alist (fs)
  "The loeb function, specialized to alists. See `loeb'.
Example:
  (loeb-alist '((foo . (lambda (alist)
                          (loeb-resolve (alist-get 'bar alist))))
                (bar . (lambda (alist) 2))))
    ==> ((foo . 2)
         (bar . 2))"
  (seq-map (lambda (cell)
             (cons (car cell)
                   (thunk-force (cdr cell))))
           (loeb-alist* fs)))

(defun loeb-plist-map! (fn plist)
  "Map FN over PLIST, modifying it in-place and returning it.
FN must take two arguments: the key and the value."
  (let ((plist-index plist))
    (while plist-index
      (let ((key (pop plist-index)))
        (setf (car plist-index) (funcall fn key (car plist-index))
              plist-index (cdr plist-index)))))
  plist)

(defun loeb-plist* (fs)
  "The loeb function, specialized to plists. See `loeb'.
This version does not force all values before returning.
See `loeb-plist' for more information."
  (letrec ((go (loeb-plist-map!
                (lambda (_key value)
                  (thunk-delay (funcall value go)))
                fs)))
    go))

(defun loeb-plist (fs)
  "The loeb function, specialized to plists. See `loeb'.
Example:
  (loeb-plist '(:foo (lambda (plist)
                        (loeb-resolve (plist-get plist :bar)))
                :bar (lambda (plist) 2)))
    ==> (:foo 2 :bar 2)"
  (loeb-plist-map! (lambda (_key value) (thunk-force value))
                   (loeb-plist* fs)))

(defalias 'loeb-resolve 'thunk-force)

(defsubst loeb-get (key alist)
  "Version of `alist-get' to be used with `loeb' and friends."
  (loeb-resolve (alist-get key alist)))

(defun loeb-alist-overlays (&rest overlays)
  "Resolve all of the given alist OVERLAYS.
Each overlay in OVERLAYS has the following general type:

  [(SYMBOL × (FINAL-ALIST → PARENT-ALIST → VALUE))]

The function used for the \"value\" within each overlay receives
two alists: the \"final\" closure after all overlays are
performed, and the state of the closure just prior to that
overlay.

Note: this scheme implements a similar logic to what is found in
nixpkgs. Here is a semi-realistic example:

  (loeb-alist-overlays
     '((foo . (lambda (final _parent)
                (1+ (loeb-get 'bar final))))
       (bar . (lambda (_final _parent)
                123)))
     '((bar . (lambda (final parent)
                (+ 100 (loeb-get 'bar parent)))))
     '((foo . (lambda (final parent)
                (+ 100 (loeb-get 'foo parent))))
       (baz . (lambda (final parent)
                (+ 100 (loeb-get 'foo final))))))
    ==>
      ((baz . 424)
       (bar . 223)
       (foo . 324))

Unfortunately, because Emacs Lisp does not have efficient
immutable data structures, each generation of the alist between
overlays must be copied \"in the spine\", which wastes as many
cons cells as there are keys in each generation, plus the thunk
closure created for each value of that generation."
  (loeb-alist
   (seq-reduce
    #'(lambda (acc overlay)
        ;; `acc' must be copied eagerly here, because the loop below is likely
        ;; to modify it in place. The loebed version, however, can wait until
        ;; it is first needed by `loeb-get'.
        (let* ((parent (copy-alist acc))
               (loebed (thunk-delay (loeb-alist* parent))))
          (dolist (entry overlay)
            (setf (alist-get (car entry) acc)
                  #'(lambda (final)
                      (funcall (cdr entry) final (thunk-force loebed)))))
          acc))
    overlays
    nil)))

(provide 'loeb)
