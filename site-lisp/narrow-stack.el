;;; narrow-stack version 1.0
;;
;; Copyright (C) 1999 Jesper Kjær Pedersen <blackie@ifad.dk>
;;
;; Author: Jesper Kjær Pedersen <blackie@ifad.dk>
;; Home page: http://www.imada.sdu.dk/~blackie/emacs/
;; Created: 18 Apr. 1999
;; Keywords: narrow

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, you can either send email to this
;; program's maintainer or write to: The Free Software Foundation,
;; Inc.; 59 Temple Place, Suite 330; Boston, MA 02111-1307, USA.

;;; Commentary:
;; Narrowing, as implemented in Emacs has one limitation, which I find very
;; annoying, namely that it is not possible to narrow within a narrowing,
;; and then widen again to the previous narrowing.
;; This package implements an extension to narrowing, which makes this
;; possible.
;;
;; This package has been developed as part of my job on writing the book
;; "Sams Teach yourself Emacs in 24 hours".
;; For more information about this book, please go to the page www.mcp.com
;; and search for the word Emacs.
;;
;; To install this package, copy this file to a directory in your load-path
;; and insert the following into your .emacs file:
;; (require 'narrow-stack)
;; (narrow-stack-mode)

;;; History Information
;; 1.0.1 Added documentation for functions
;; 1.0   First official relase.

(require 'advice)
(defvar ns-stack '()
  "the stack of earlier narrows")
(make-variable-buffer-local 'ns-stack)

(defvar narrow-stack-mode nil
  "narrow-stack-mode implements a stack of narrows. Thus with
narrow-stack-mode you may narrow within narrowing, and widen to the
previous narrowing\n\nFor more information on narrowing, see narrow-to-region")

(defun ns-narrow-to-region (start end)
  "narrow to the region marked, in a way, which makes it possible to widen
to the given view later.\n\nFor more information on narrowing, see narrow-to-region"
  (interactive "r")
  (let* ((pm (point-marker))
	(ns-elm (list (point-min) pm)))
    (set-marker pm (+ 1 (point-max)))
    (if (and (null ns-stack) (ns-is-narrowed))
	(progn
	  ;; narrow-stack do not have any information about
	  ;; narrowing of this buffer, though it is narrowed.
	  ;; Push an extra element to the stack, to avoid that the function
	  ;; widen rather than ns-widen is called, when this element is widened.
	  (setq ns-stack (cons ns-elm (cons ns-elm ns-stack))))
      (setq ns-stack (cons ns-elm  ns-stack)))
    (narrow-to-region start end)))

(defun ns-widen ()
  "widen the view to the previous narrowing, or to the whole view if no
previous narrowing exists.\n\nFor more information on narrowing, see narrow-to-region"
  (interactive "")
  (if (<= (length ns-stack) 1)
      ; One element on the stack means that only one level of narrowing
      ; exists. Thus narrowing should be disabled.
      (widen)
    (let ((new-start (caar ns-stack))
	  (new-end   (- (cadar ns-stack) 1)))
      (progn
	(setq ns-stack (cdr ns-stack))
	(narrow-to-region new-start new-end)

	;; Delete the marker. Is this necessary?
	;(set-marker new-end nil)
	))))

(defun ns-is-narrowed ()
  (or (not (= (point-min) 1)) (not (= (1+ (buffer-size)) (point-max)))))

(defun narrow-stack-mode (&optional arg)
"narrow-stack-mode implements a stack of narrows. Thus with
narrow-stack-mode you may narrow within narrowing, and widen to the
previous narrowing\n\nFor more information on narrowing, see narrow-to-region"
  (interactive "P")
  (setq narrow-stack-mode
	(if (null arg)
	    (not narrow-stack-mode)
	  (> (prefix-numeric-value arg) 0)))
  (if narrow-stack-mode
      (progn
	(substitute-key-definition 'narrow-to-region 'ns-narrow-to-region global-map)
	(substitute-key-definition 'widen 'ns-widen global-map)
	(ad-enable-advice 'widen 'before 'ns-widen-advice))
    (progn
      (substitute-key-definition 'ns-narrow-to-region 'narrow-to-region  global-map)
      (substitute-key-definition 'ns-widen 'widen global-map)
      (ad-disable-advice 'widen 'before 'ns-widen-advice)))
  (ad-activate 'widen))

(defadvice widen (before ns-widen-advice dis)
  (setq ns-stack '()))

(provide 'narrow-stack)
