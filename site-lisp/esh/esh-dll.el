;;; esh-dll.el --- Doubly-linked-list data structure        -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement@clem-w50-mint>
;; Keywords: tools, internal, data

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

;;; Code:

(defun esh-dll-val (dll) "Get current element of DLL." (nth 0 dll))
(defun esh-dll-prev (dll) "Get PREV link of DLL." (nth 1 dll))
(defun esh-dll-next (dll) "Get NEXT link of DLL." (nth 2 dll))

(gv-define-setter esh-dll-prev (prev dll) `(setf (nth 1 ,dll) ,prev))
(gv-define-setter esh-dll-next (next dll) `(setf (nth 2 ,dll) ,next))

(defun esh-dll-new (val prev next)
  "Create new link (VAL PREV NEXT).
Updates PREV and NEXT to point to new link."
  (let ((new (list val prev next)))
    (when prev (setf (esh-dll-next prev) new))
    (when next (setf (esh-dll-prev next) new))
    new))

(defmacro esh-dll-push-front (e dll)
  "Insert E into doubly-linked list DLL."
  `(setq ,dll (esh-dll-new ,e (and ,dll (esh-dll-prev ,dll)) ,dll)))

(defun esh-dll-pop (dll)
  "Remove first element of doubly-linked list DLL.
Returns updated list.  Beware of the fact that if DLL is the
first link of a doubly-linked list, the caller must update it
using something like (setq dll (esh-dll-pop dll))."
  (pcase dll
    (`nil (error "Popping from empty list"))
    (`(,_ ,prev ,next)
     (when prev (setf (esh-dll-next prev) next))
     (when next (setf (esh-dll-prev next) prev))
     next)))

(defun esh-dll-first (dll)
  "Rewind to beginning of doubly-linked list DLL."
  (let ((first nil))
    (while dll
      (setq first dll)
      (setq dll (esh-dll-prev dll)))
    first))

(defun esh-dll-to-list (dll)
  "Make a list from DLL."
  (setq dll (esh-dll-first dll))
  (let ((acc nil))
    (while dll
      (push (esh-dll-val dll) acc)
      (setq dll (esh-dll-next dll)))
    (nreverse acc)))

(defun esh-dll-from-list (ls)
  "Make a doubly-linked list from LS."
  (let ((dll nil))
    (dolist (elem (reverse ls))
      (esh-dll-push-front elem dll))
    dll))

;; (esh-dll-to-list (esh-dll-from-list '((1 2 3) (4 5 6) 7 8 9)))

(provide 'esh-dll)
;;; esh-dll.el ends here
