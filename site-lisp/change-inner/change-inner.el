;;; change-inner.el --- Change contents based on semantic units

;; Copyright (C) 2012 Magnar Sveen <magnars@gmail.com>

;; Author: Magnar Sveen <magnars@gmail.com>
;; Version: 0.2.0
;; Keywords: convenience, extensions
;; Package-Requires: ((expand-region "0.7"))

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

;; # change-inner.el
;;
;; change-inner gives you vim's `ci` command, building on
;; [expand-region](https://github.com/magnars/expand-region.el). It is most easily
;; explained by example:
;;
;;     function test() {
;;       return "semantic kill";
;;     }
;;
;; With point after the word `semantic`
;;
;;  * `change-inner "` would kill the contents of the string
;;  * `change-outer "` would kill the entire string
;;  * `change-inner {` would kill the return-statement
;;  * `change-outer {` would kill the entire block
;;
;; I use `M-i` and `M-o` for this.
;;
;; Giving these commands a prefix argument `C-u` means copy instead of kill.
;;
;; ## Installation
;;
;; Start by installing
;; [expand-region](https://github.com/magnars/expand-region.el).
;;
;;     (require 'change-inner)
;;     (global-set-key (kbd "M-i") 'change-inner)
;;     (global-set-key (kbd "M-o") 'change-outer)
;;
;; ## It's not working in my favorite mode
;;
;; That may just be because expand-region needs some love for your mode. Please
;; open a ticket there: https://github.com/magnars/expand-region.el

;;; Code:

(require 'expand-region)

(eval-when-compile (require 'cl))

(defun ci--flash-region (start end)
  "Temporarily highlight region from START to END."
  (let ((overlay (make-overlay start end)))
    (overlay-put overlay 'face 'secondary-selection)
    (overlay-put overlay 'priority 100)
    (run-with-timer 0.2 nil 'delete-overlay overlay)))

(defun change-inner* (yank? search-forward-char)
  "Works like vim's ci command. Takes a char, like ( or \" and
kills the innards of the first ancestor semantic unit starting with that char."
  (let* ((expand-region-fast-keys-enabled nil)
         (char (or search-forward-char
                   (char-to-string
                    (read-char
                     (if yank?
                         "Yank inner, starting with:"
                       "Change inner, starting with:")))))
         (q-char (regexp-quote char))
         (starting-point (point)))
    (when search-forward-char
      (search-forward char (point-at-eol)))
    (flet ((message (&rest args) nil))
      (er--expand-region-1)
      (er--expand-region-1)
      (while (and (not (= (point) (point-min)))
                  (not (looking-at q-char)))
        (er--expand-region-1))
      (if (not (looking-at q-char))
          (if search-forward-char
              (error "Couldn't find any expansion starting with %S" char)
            (goto-char starting-point)
            (setq mark-active nil)
            (change-inner* yank? char))
        (er/contract-region 1)
        (if yank?
            (progn
              (copy-region-as-kill (region-beginning) (region-end))
              (ci--flash-region (region-beginning) (region-end))
              (goto-char starting-point))
          (kill-region (region-beginning) (region-end)))))))

;;;###autoload
(defun change-inner (arg)
  (interactive "P")
  (change-inner* arg nil))

;;;###autoload
(defun copy-inner ()
  (interactive)
  (change-inner* t nil))

(defun change-outer* (yank? search-forward-char)
  "Works like vim's ci command. Takes a char, like ( or \" and
kills the first ancestor semantic unit starting with that char."
  (let* ((expand-region-fast-keys-enabled nil)
         (char (or search-forward-char
                   (char-to-string
                    (read-char
                     (if yank?
                         "Yank outer, starting with:"
                       "Change outer, starting with:")))))
         (q-char (regexp-quote char))
         (starting-point (point)))
    (when search-forward-char
      (search-forward char (point-at-eol)))
    (flet ((message (&rest args) nil))
      (when (looking-at q-char)
        (er/expand-region 1))
      (while (and (not (= (point) (point-min)))
                  (not (looking-at q-char)))
        (er/expand-region 1))
      (if (not (looking-at q-char))
          (if search-forward-char
              (error "Couldn't find any expansion starting with %S" char)
            (goto-char starting-point)
            (setq mark-active nil)
            (change-outer* yank? char))
        (if yank?
            (progn
              (copy-region-as-kill (region-beginning) (region-end))
              (ci--flash-region (region-beginning) (region-end))
              (goto-char starting-point))
          (kill-region (region-beginning) (region-end)))))))

;;;###autoload
(defun change-outer (arg)
  (interactive "P")
  (change-outer* arg nil))

;;;###autoload
(defun copy-outer ()
  (interactive)
  (change-outer* t nil))

(provide 'change-inner)
;;; change-inner.el ends here
