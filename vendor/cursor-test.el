;;; cursor-test.el --- testing library for cursor position in emacs. -*- lexical-binding: t; -*-

;; Copyright (C) 2013 by Satsohi Namai

;; Author: ainame
;; URL: https://github.com/ainame/cursor-test.el
;; Version: 0.1.0
;; Package-Requires: ((emacs "24"))

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
;;;
;;; see: https://github.com/ainame/cursor-test.el
;;;

;;; Code:

(require 'cl)
(require 'ert)

(defvar cursor-test/cursor-char "|"
  "The representation of cursor in `cursor-test` library.")

(defun cursor-test/setup-cursor (cursor-char)
  (goto-char (point-max))
  (re-search-backward cursor-char nil t)
  (delete-char (length cursor-char)))

(defun cursor-test/setup-test-buffer (func)
  "call func at test-buffer and return test-buffer"
  (let ((test-buffer (generate-new-buffer "*cursor-test-test*"))
        (curr-buf (current-buffer)))
    (switch-to-buffer test-buffer)
    (funcall func)
    (switch-to-buffer curr-buf)
    test-buffer))

(defun cursor-test/insert-cursor-char ()
  (insert cursor-test/cursor-char))

(defun* cursor-test/pretty-format-cursor (buffer)
  (with-current-buffer buffer
    (cursor-test/insert-cursor-char)
    (buffer-substring-no-properties (point-min) (point-max))))

(defun* cursor-test/setup (&key init exercise)
  "`cursor-test/setup` works for creating argument value of `cursor-test/equal`.
INIT is the initialize value of buffer which is the string. In INIT string,
you can declare cursor position by `|` which defined at `cursor-test/cursor-char`."
  (cursor-test/setup-test-buffer
   (lambda ()
     (insert init)
     (cursor-test/setup-cursor cursor-test/cursor-char)
     (if exercise (funcall exercise)))))

(defun cursor-test/get-cursor-pos ()
  (list (current-column) (line-number-at-pos)))

(defun cursor-test/compare-pos (pos1 pos2)
  (let ((column-result   (= (car  pos1) (car  pos2)))
        (line-num-result (= (cadr pos1) (cadr pos2))))
    (and column-result line-num-result)))

(defun* cursor-test/compare-cursor-pos (&key compare description expect actual)
  (let* ((expect-pos (with-current-buffer expect (cursor-test/get-cursor-pos)))
         (actual-pos (with-current-buffer actual (cursor-test/get-cursor-pos)))
         (result (if (eq compare 'equal)
                     (cursor-test/compare-pos expect-pos actual-pos)
                   (not (cursor-test/compare-pos expect-pos actual-pos)))))
    (if result
        t
      (progn
        (princ (if description
                     (format "Fail test: %s" description)
                   "Fail test"))
        (princ (format "[buffer]\n expect: \"%s\"\n actual: \"%s\""
                         (cursor-test/pretty-format-cursor expect)
                         (cursor-test/pretty-format-cursor actual)))
        (princ (format "[position] expect: (%d, %d), actual: (%d, %d)"
                         (car expect-pos) (cadr expect-pos) (car actual-pos) (cadr actual-pos)))
        nil))))

(defun* cursor-test/compare-cursor-point (&key compare description expect actual)
  (let* ((expect-point (with-current-buffer expect (point)))
         (actual-point (with-current-buffer actual (point)))
         (result (if (eq compare 'equal)
                     (= expect-point actual-point)
                   (not (= expect-point actual-point)))))
    (if result
        t
      (progn
        (message (if description
                     (format "Fail test: %s" description)
                   "Fail test"))
        (message (format "[buffer]\n expect: \"%s\"\n actual: \"%s\""
                         (cursor-test/pretty-format-cursor expect)
                         (cursor-test/pretty-format-cursor actual)))
        (message (format "[point] expect: %d, actual: %d" expect-point actual-point))
        nil))))

(defun* cursor-test/compare-buffer (&key compare description expect actual type)
  (cond ((eq type 'pos) (cursor-test/compare-cursor-pos
                         :compare compare :description description :expect expect :actual actual))
        ((eq type 'point) (cursor-test/compare-cursor-point
                           :compare compare :description description :expect expect :actual actual))
        (t (cursor-test/compare-cursor-point
            :compare compare :description description :expect expect :actual actual))))

(defun* cursor-test/equal (&key description expect actual type)
  "`cursor-test/equal` is the assert for equal of cursor position between two buffers.
EXPECT and ACTUAL are buffer in emacs that contain the infomation of cursor position."
  (should
   (cursor-test/compare-buffer :compare 'equal :description description :expect expect :actual actual :type type)))

(defun* cursor-test/not-equal (&key description expect actual type)
  (should-not
   (cursor-test/compare-buffer :compare 'not-equal :description description :expect expect :actual actual :type type)))


(defun* cursor-test/equal* (&key description init exercise expect type)
  "`cursor-test/equal*` is the shorthand version of `cursor-test/equal`.
This function's arguments contain their's one."
  (cursor-test/equal
   :type type
   :description description
   :expect (cursor-test/setup :init expect)
   :actual (cursor-test/setup :init init :exercise exercise)))

(defun* cursor-test/not-equal* (&key type description init exercise expect)
  (cursor-test/not-equal
   :type type
   :description description
   :expect (cursor-test/setup :init expect)
   :actual (cursor-test/setup :init init :exercise exercise)))

(provide 'cursor-test)
;;; cursor-test.el ends here
