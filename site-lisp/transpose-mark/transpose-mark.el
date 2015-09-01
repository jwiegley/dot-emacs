;;; transpose-mark.el --- Transpose data using the Emacs mark

;; Copyright (C) 2015  Kevin W. van Rooijen

;; Author: Kevin W. van Rooijen <kevin.van.rooijen@attichacker.com>
;; Keywords: transpose, convenience

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
;;
;; A small libary that lets you transpose data by leaving an Emacs mark on the
;; line you want to transpose.
;;
;; Functions:
;;
;; * transpose-mark
;; * transpose-mark-line
;; * transpose-mark-region
;;
;; Faces:
;;
;; * transpose-mark-region-set-face
;;
;;; Code:

(defgroup transpose-mark nil
  "Transpose Mark group."
  :prefix "transpose-mark-")

(defface transpose-mark-region-set-face
  '((t :background "#7700ff" :foreground "#ffffff"))
  "Transpose Marked region overlay face" :group 'transpose-mark)

(defvar transpose-mark-region-overlay 'nil "Overlay for Transpose Mark Region.")

;;;###autoload
(defun transpose-mark ()
  "If region is active use 'transpose-mark-region', otherwise use 'transpose-mark-line'."
  (interactive)
  (if (region-active-p) (transpose-mark-region) (transpose-mark-line)))

;;;###autoload
(defun transpose-mark-line ()
  "Transpose the current line with the line which the current mark is pointing to."
  (interactive)
  (transpose-mark-delete-overlay)
  (let ((col (current-column)))
    (save-excursion
      (beginning-of-line)
      (kill-line)
      (pop-to-mark-command)
      (beginning-of-line)
      (yank)
      (kill-line))
    (yank)
    (pop-mark)
    (move-to-column col)))

;;;###autoload
(defun transpose-mark-region ()
  "Transpose the current region with the previously marked region.
Once you've transposed one the region is reset."
  (interactive)
  (if (transpose-mark-region-overlay-active)
      (let* ((current-region (buffer-substring-no-properties (mark) (point)))
             (target-start (overlay-start transpose-mark-region-overlay))
             (target-end (overlay-end transpose-mark-region-overlay))
             (target-region (buffer-substring-no-properties target-start target-end)))
        (if (> (mark) target-start)
            (progn
              (transpose-mark-region-set-current target-region)
              (transpose-mark-region-set-target target-start target-end current-region))
          (progn
            (transpose-mark-region-set-target target-start target-end current-region)
            (transpose-mark-region-set-current target-region)))
        (transpose-mark-delete-overlay))
    (transpose-mark-save-point)))

;;;###autoload
(defun transpose-mark-region-abort ()
  "Remove the transpose-mark-region-overlay if set."
  (interactive)
  (transpose-mark-delete-overlay))

;;;###autoload
(defun transpose-mark-region-start-func (func)
  "Run a function at the start of the overlay and expand the overlay selection to
the new point after the function as been ran."
  (interactive)
  (if (transpose-mark-region-overlay-active)
      (save-excursion
        (let ((target-end (overlay-end transpose-mark-region-overlay)))
          (goto-char (overlay-start transpose-mark-region-overlay))
          (call-interactively func)
          (transpose-mark-delete-overlay)
          (setq-local transpose-mark-region-overlay (make-overlay (point) target-end))
          (overlay-put transpose-mark-region-overlay 'face 'transpose-mark-region-set-face)))))

;;;###autoload
(defun transpose-mark-region-end-func (func)
  "Run a function at the end of the overlay and expand the overlay selection to
the new point after the function as been ran."
  (interactive)
  (if (transpose-mark-region-overlay-active)
      (save-excursion
        (let ((target-start (overlay-start transpose-mark-region-overlay)))
          (goto-char (overlay-end transpose-mark-region-overlay))
          (call-interactively func)
          (transpose-mark-delete-overlay)
          (setq-local transpose-mark-region-overlay (make-overlay target-start (point)))
          (overlay-put transpose-mark-region-overlay 'face 'transpose-mark-region-set-face)))))

;;;
;;; Transpose Mark Region Expand Start Functions
;;;

;;;###autoload
(defun tmr-start--forward-word ()
  "Run transpose-mark-region-start-func with forward-word."
  (interactive)
  (transpose-mark-region-start-func 'forward-word))
;;;###autoload
(defun tmr-start--backward-word ()
  "Run transpose-mark-region-start-func with backward-word."
  (interactive)
  (transpose-mark-region-start-func 'backward-word))
;;;###autoload
(defun tmr-start--forward-char ()
  "Run transpose-mark-region-start-func with forward-char."
  (interactive)
  (transpose-mark-region-start-func 'forward-char))
;;;###autoload
(defun tmr-start--backward-char ()
  "Run transpose-mark-region-start-func with backward-char."
  (interactive)
  (transpose-mark-region-start-func 'backward-char))

;;;
;;; Transpose Mark Region Expand End Functions
;;;

;;;###autoload
(defun tmr-end--forward-word ()
  "Run transpose-mark-region-end-func with forward-word."
  (interactive)
  (transpose-mark-region-end-func 'forward-word))
;;;###autoload
(defun tmr-end--backward-word ()
  "Run transpose-mark-region-end-func with backward-word."
  (interactive)
  (transpose-mark-region-end-func 'backward-word))
;;;###autoload
(defun tmr-end--forward-char ()
  "Run transpose-mark-region-end-func with forward-char."
  (interactive)
  (transpose-mark-region-end-func 'forward-char))
;;;###autoload
(defun tmr-end--backward-char ()
  "Run transpose-mark-region-end-func with backward-char."
  (interactive)
  (transpose-mark-region-end-func 'backward-char))


;;;
;;; Private Functions
;;;
(defun transpose-mark-region-set-target (target-start target-end current-region)
  "Set the value of the target region."
  (kill-region target-start target-end)
  (transpose-mark--insert-at-point current-region (min target-start target-end)))

(defun transpose-mark-region-set-current (target-region)
  "Set the value of the current region."
  (kill-region (mark) (point))
  (insert target-region))

(defun transpose-mark-save-point ()
  "Create an overlay on the region set for tranposition."
  (deactivate-mark nil)
  (setq-local transpose-mark-region-overlay (make-overlay (mark) (point)))
  (overlay-put transpose-mark-region-overlay 'face 'transpose-mark-region-set-face)
  (message "Transpose Mark Region set!"))

(defun transpose-mark--insert-at-point (string point)
  "Insert a string at a given point."
  (save-excursion
    (goto-char point)
    (insert string)))

(defun transpose-mark-delete-overlay ()
  "Delete transpose-mark-region-overlay if it exists."
  (if (transpose-mark-region-overlay-active) (delete-overlay transpose-mark-region-overlay)))

(defun transpose-mark-region-overlay-active ()
  "Check if transpose-mark-region-overlay is active."
  (and transpose-mark-region-overlay
       (overlay-start transpose-mark-region-overlay)))

(provide 'transpose-mark)
;;; transpose-mark.el ends here
