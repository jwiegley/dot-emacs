;;; indent-shift.el --- Shift indentation            -*- lexical-binding: t; -*-

;; Copyright (C) 2014  Tom Willemse

;; Author: Tom Willemse <tom@ryuslash.org>
;; Keywords: convenience
;; Version: 1.0.0

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

;; Functions copied from `python-mode.el' to work more generally.

;;; Code:

;;;###autoload
(defun indent-shift-left (start end &optional count)
  "Rigidly indent region.
Region is from START to END.  Move
COUNT number of spaces if it is non-nil otherwise use
`tab-width'."
  (interactive
   (if mark-active
       (list (region-beginning) (region-end) current-prefix-arg)
     (list (line-beginning-position)
           (line-end-position)
           current-prefix-arg)))
  (if count
      (setq count (prefix-numeric-value count))
    (setq count tab-width))
  (when (> count 0)
    (let ((deactivate-mark nil))
      (save-excursion
        (goto-char start)
        (while (< (point) end)
          (if (and (< (current-indentation) count)
                   (not (looking-at "[ \t]*$")))
              (error "Can't shift all lines enough"))
          (forward-line))
        (indent-rigidly start end (- count))))))

;;;###autoload
(defun indent-shift-right (start end &optional count)
  "Indent region between START and END rigidly to the right.
If COUNT has been specified indent by that much, otherwise look at
`tab-width'."
  (interactive
   (if mark-active
       (list (region-beginning) (region-end) current-prefix-arg)
     (list (line-beginning-position)
           (line-end-position)
           current-prefix-arg)))
  (let ((deactivate-mark nil))
    (if count
        (setq count (prefix-numeric-value count))
      (setq count tab-width))
    (indent-rigidly start end count)))

(add-to-list 'debug-ignored-errors "^Can't shift all lines enough")

(provide 'indent-shift)
;;; indent-shift.el ends here
