;;; shift-number.el --- Increase/decrease the number at point

;; Copyright © 2016–2017 Alex Kost

;; Author: Alex Kost <alezost@gmail.com>
;; Created: 12 Apr 2016
;; Version: 0.1
;; URL: https://github.com/alezost/shift-number.el
;; Keywords: convenience

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Increase or decrease the number at point with `shift-number-up' and
;; `shift-number-down' commands.

;; To install the package manually, add the following to your init file:
;;
;; (add-to-list 'load-path "/path/to/shift-number-dir")
;; (autoload 'shift-number-up "shift-number" nil t)
;; (autoload 'shift-number-down "shift-number" nil t)

;; For more verbose description and a gif demonstration, see
;; <https://github.com/alezost/shift-number.el>.

;;; Code:

(defgroup shift-number nil
  "Increase or decrease the number at point."
  :group 'convenience)

(defcustom shift-number-regexp
  (rx (group (one-or-more num)))
  "Regexp for `shift-number' function.
The first parenthesized expression must match the number."
  :type 'regexp
  :group 'shift-number)

(defcustom shift-number-display-message nil
  "If non-nil, display a message after shifting the current number."
  :type 'boolean
  :group 'shift-number)

(defun shift-number-in-regexp-p (regexp)
  "Return non-nil, if point is inside REGEXP on the current line."
  ;; The code originates from `org-at-regexp-p'.
  (save-excursion
    (let ((pos (point))
          (end (line-end-position))
          found exit)
      (beginning-of-line)
      (while (and (not (or exit found))
                  (re-search-forward regexp end t))
        (cond
         ((> (match-beginning 0) pos)
          (setq exit t))
         ((>= (match-end 0) pos)
          (setq found t))))
      found)))

(defun shift-number (n)
  "Change the number at point by N.
If there is no number at point, search forward till the end of
the current line and change it."
  ;; The whole number is removed and a new number is inserted in its
  ;; place, so `save-excursion' is not used, as it will put the point at
  ;; the beginning of the number.  Instead, the point is saved and
  ;; restored later.
  (let ((old-pos (point)))
    (or (shift-number-in-regexp-p shift-number-regexp)
        (re-search-forward shift-number-regexp (line-end-position) t)
        (error "No number on the current line"))
    (let* ((beg         (match-beginning 1))
           (end         (match-end       1))
           (old-num-str (buffer-substring-no-properties beg end))
           (old-num     (string-to-number old-num-str))
           (new-num     (+ old-num n))
           (new-num-str (number-to-string new-num)))
      (delete-region beg end)
      ;; If there are leading zeros, preserve them keeping the same
      ;; length of the original number.
      (when (string-match-p "\\`0" old-num-str)
        (let ((len-diff (- (length old-num-str)
                           (length new-num-str))))
          (when (> len-diff 0)
            (insert (make-string len-diff ?0)))))
      (insert new-num-str)
      (goto-char old-pos)
      (when shift-number-display-message
        (message "Number %d has been changed to number %d."
                 old-num new-num)))))

;;;###autoload
(defun shift-number-up (&optional arg)
  "Increase the number at point (or on the current line) by ARG."
  (interactive "p")
  (shift-number arg))

;;;###autoload
(defun shift-number-down (&optional arg)
  "Decrease the number at point (or on the current line) by ARG."
  (interactive "p")
  (shift-number (- arg)))

(provide 'shift-number)

;;; shift-number.el ends here
