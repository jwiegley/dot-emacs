;;; circe-compat.el --- Compatibility definitions

;; Copyright (C) 2015  Jorgen Schaefer <contact@jorgenschaefer.de>

;; Author: Jorgen Schaefer <contact@jorgenschaefer.de>

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Define functions and variables as needed by Circe to remain
;; compatible with older Emacsen.

;;; Code:

(when (not (fboundp 'string-trim))
  (defun string-trim (string)
    "Remove leading and trailing whitespace from STRING."
    (if (string-match "\\` *\\(.*[^[:space:]]\\) *\\'" string)
        (match-string 1 string)
      string)))

(when (not (fboundp 'add-face-text-property))
  (defun add-face-text-property (start end face &optional append object)
    (while (/= start end)
      (let* ((next (next-single-property-change start 'face object end))
             (prev (get-text-property start 'face object))
             (value (if (listp prev) prev (list prev))))
        (put-text-property start next 'face
                           (if append
                               (append value (list face))
                             (append (list face) value))
                           object)
        (setq start next)))))

(when (not (boundp 'mode-line-misc-info))
  (defvar mode-line-misc-info nil
    "Misc info in the mode line.")
  (add-to-list 'mode-line-format 'mode-line-misc-info t))

(provide 'circe-compat)
;;; circe-compat.el ends here
