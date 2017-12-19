;;; smart-region.el --- Smartly select region, rectangle, multi cursors

;;-------------------------------------------------------------------
;;
;; Copyright (C) 2015 Yuuki Arisawa
;;
;; This file is NOT part of Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free
;; Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA
;;
;;-------------------------------------------------------------------

;; Author: Yuuki Arisawa <yuuki.ari@gmail.com>
;; URL: https://github.com/uk-ar/smart-region
;; Package-Requires: ((emacs "24.4") (expand-region "0.10.0") (multiple-cursors "1.3.0") (cl-lib "0.5"))
;; Created: 1 April 2015
;; Version: 1.0
;; Keywords: marking region
;;; Compatibility: GNU Emacs 24.4

;;; Commentary:

;; Smart region guesses what you want to select by one command:

;; - If you call this command multiple times at the same position, it
;;   expands the selected region (with `er/expand-region').
;; - Else, if you move from the mark and call this command, it selects
;;   the region rectangular (with `rectangle-mark-mode').
;; - Else, if you move from the mark and call this command at the same
;;   column as mark, it adds a cursor to each line (with `mc/edit-lines').

;; This basic concept is from sense-region: https://gist.github.com/tnoda/1776988.

(require 'expand-region)
(require 'multiple-cursors)
(require 'cl-lib)

;;; Code:
(defun smart-region-check-er(func)
  (let ((before (cons (mark) (point))))
    (funcall func)
    (not (equal (cons (mark) (point)) before))))

;;TODO: u C-SPC for pop mark
;;;###autoload
(defun smart-region (arg)
  "Smart region guess what you want to select by one command.
If you call this command multiple times at the same position, it expands
selected region (it calls `er/expand-region').
Else, if you move from the mark and call this command, it select the
region rectangular (it call `rectangle-mark-mode').
Else, if you move from the mark and call this command at same column as
mark, it add cursor to each line (it call `mc/edit-lines')."
  (interactive "P")
  (cond
   ;;region not exist
   ((not (region-active-p))
    (setq this-command 'set-mark-command)
    (call-interactively 'set-mark-command))
   ;;region exist & single line
   ((= (line-number-at-pos) (line-number-at-pos (mark)))
    ;;(setq this-command 'er/expand-region)
    ;;https://github.com/magnars/expand-region.el/issues/31
    (cl-case (char-syntax (char-after))
      (?\"
       (unless (smart-region-check-er 'er/mark-outside-quotes)
         (call-interactively 'er/expand-region)))
      ((?\) ?\()
       (unless (smart-region-check-er 'er/mark-outside-pairs)
         (call-interactively 'er/expand-region)))
      (t (call-interactively 'er/expand-region))))
   ;; region exist & multi line
   (t
    (let ((column-of-mark
           (save-excursion
             (goto-char (mark))
             (current-column))))
      (if (eq column-of-mark (current-column))
          (call-interactively 'mc/edit-lines)
        (call-interactively 'rectangle-mark-mode))))))

;;;###autoload
(defun smart-region-on ()
  "Set C-SPC to smart-region."
  (interactive)
  (define-key global-map [remap set-mark-command] 'smart-region)
  )

;;;###autoload
(defun smart-region-off ()
  "Reset C-SPC to original command."
  (interactive)
  (define-key global-map [remap set-mark-command] nil)
  )

(add-to-list 'mc/cmds-to-run-once
             'smart-region)
;; settings
(setq mc/cmds-to-run-for-all
      (delq 'smart-region
            mc/cmds-to-run-for-all))

(mc/save-lists)

(provide 'smart-region)
;;; smart-region.el ends here
