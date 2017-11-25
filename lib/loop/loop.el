;;; loop.el --- friendly imperative loop structures

;; Copyright (C) 2013 Wilfred Hughes

;; Author: Wilfred Hughes <me@wilfred.me.uk>
;; Version: 1.4
;; Keywords: loop, while, for each, break, continue

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

;; Emacs lisp is missing loop structures familiar to users of newer
;; languages. This library adds a selection of popular loop structures
;; as well as break and continue.

;; Future ideas:

;; * Named loops so you can break/continue outer loops

(defmacro loop-while (condition &rest body)
  "Repeatedly evaluate BODY while CONDITION is non-nil."
  (declare (indent defun) (debug (form &rest form)))
  `(catch 'loop-break
     (while ,condition
       (catch 'loop-continue
         ,@body))))

(defmacro loop-do-while (condition &rest body)
  "Evaluate BODY, then repeatedly BODY while CONDITION is non-nil."
  (declare (indent defun) (debug (form &rest form)))
  (let ((is-first-iteration-var (make-symbol "first-iteration-p")))
    `(catch 'loop-break
       (progn
         (catch 'loop-continue
           ,@body)
         (while ,condition
           (catch 'loop-continue
             ,@body))))))

(defmacro loop-until (condition &rest body)
  "Repeatedly evaluate BODY until CONDITION is non-nil."
  (declare (indent defun) (debug (form &rest form)))
  `(loop-while (not ,condition) ,@body))

;; todo: support vectors and strings
(defmacro loop-for-each (var list &rest body)
  "For every item in LIST, evaluate BODY with VAR bound to that item."
  (declare (indent defun) (debug (symbolp form &rest form)))
  (let ((list-var (make-symbol "list")))
    `(catch 'loop-break
       (let ((,list-var ,list)
             (,var))
         (while ,list-var
           (catch 'loop-continue
             (setq ,var (car ,list-var))
             (setq ,list-var (cdr ,list-var))
             ,@body))))))

(defun loop--last-line-p ()
  "Return non-nil if point is on the last line in the buffer."
  (looking-at (rx (0+ not-newline) buffer-end)))

(defun loop--current-line ()
  "Return the current line that contains point."
  (save-excursion
    (let ((line-start (progn (beginning-of-line) (point)))
          (line-end (progn (end-of-line) (point))))
      (buffer-substring line-start line-end))))

(defmacro loop-for-each-line (&rest body)
  "Execute BODY for every line in the buffer.
Point is placed at the start of the line on each iteration.

Inside BODY, `it' is bound to the contents of the current line."
  (declare (indent 0) (debug (&rest form)))
  `(save-excursion
     (catch 'loop-break
       (goto-char (point-min))
       ;; Execute body on all but the last line.
       (while (not (loop--last-line-p))
         (catch 'loop-continue
           (save-excursion
             (let ((it (loop--current-line)))
               ,@body)))
         (forward-line))
       ;; Execute body on the last line.
       (catch 'loop-continue
         (let ((it (loop--current-line)))
           ,@body)))))

(defsubst loop-break ()
  "Terminate evaluation of a `loop-while', `loop-do-while', or `loop-for-each' block.
If there are nested loops, breaks out of the innermost loop."
  (throw 'loop-break nil))

(defun loop-continue ()
  "Skip the rest of the current `loop-while', `loop-do-while', or
`loop-for-each' block and continue to the next iteration. If there
are nested loops, applies to the innermost loop."
  (throw 'loop-continue nil))


(defun loop-return (value)
  "Terminate evaluation of a `loop-while', `loop-do-while', or `loop-for-each' block.
The return value from the loop is VALUE."
  (throw 'loop-break value))

(provide 'loop)
;;; loop.el ends here
