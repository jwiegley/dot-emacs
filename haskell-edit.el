;;; haskell-edit --- Tools for editing and refactoring Haskell code

;; Copyright (C) 2013 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 24 Mar 2013
;; Version: 1.0
;; Keywords: haskell programming code
;; X-URL: https://github.com/jwiegley/haskell-edit

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Tools for editing and refactoring Haskell code.

(defgroup haskell-edit nil
  "Tools for editing and refactoring Haskell code"
  :group 'haskell-mode)

(defun haskell-find-type-signature (&optional pos)
  (save-excursion
    (if pos (goto-char pos))
    (re-search-backward "::" nil t)
    (skip-chars-backward " ")
    (let ((end (point)) beg token)
      (backward-word)
      (setq beg (point)
            token (buffer-substring beg end))
      (forward-line)
      (while (and (not (eobp))
                  (not (looking-at token)))
        (forward-line))
      (when (looking-at token)
        (cons beg (point))))))

(defun haskell-reformat-type-signature (beg end &optional format-all)
  (interactive "r")
  (save-excursion
    (save-restriction
      (let ((endr (copy-marker end t)) (lim fill-column) once)
        (narrow-to-region beg endr)
        (goto-char (point-min))
        (while (re-search-forward "[ \t\r\n][ \t\r\n]+" nil t)
          (replace-match " "))
        (when (> (- (marker-position endr) beg) lim)
          (goto-char beg)
          (looking-at "^\\(.+ \\)::")
          (let ((leader (match-string 1)))
            (if format-all
                (while (re-search-forward "\\( \\)\\([-=]> \\)" nil t)
                  (replace-match
                   (concat "\n" (make-string (length leader) ? )
                           "\\2"))
                  (if (looking-at "(")
                      (forward-sexp)))
              ;; first, just drop down the constraint if there is one
              (let ((continue t))
                (when (re-search-forward "\\( \\)\\(=> \\)" nil t)
                  (replace-match
                   (concat "\n" (make-string (length leader) ? )
                           "\\2"))
                  (setq continue
                        (> (- (line-end-position)
                              (line-beginning-position)) lim)))
                ;; if that's not enough, or if there was no constraint, try
                ;; dropping the last type
                (when continue
                  (goto-char end)
                  (when (re-search-backward "\\( \\)\\([-=]> \\)" nil t)
                    (if (> (- (point) (line-beginning-position)) lim)
                        (haskell-reformat-type-signature beg endr t)
                      (replace-match
                       (concat "\n" (make-string (length leader) ? )
                               "\\2")))))))
            (goto-char beg)
            (when (and (search-forward " :: (" (line-end-position) t)
                       (> (- (line-end-position)
                             (line-beginning-position)) lim))
              (goto-char (line-end-position))
              (let ((continue t))
                (while (and continue
                            (search-backward ", " (line-beginning-position) t))
                  (when (< (current-column) (1- lim))
                    (replace-match
                     (concat ",\n" (make-string (+ (length leader) 4) ? )))
                    (setq continue nil)))))))))))

(defun haskell-edit-reformat ()
  (interactive)
  (if (memq (get-text-property (point) 'face)
            '(font-lock-doc-face font-lock-comment-face))
      (fill-paragraph)
    (destructuring-bind (beg . end)
        (haskell-find-type-signature)
      (haskell-reformat-type-signature beg end))))

(provide 'haskell-edit)

;;; haskell-edit.el ends here
