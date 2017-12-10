;;; direx-k.el --- Display git status in direx-el -*- lexical-binding: t; -*-

;; Copyright (C) 2017 by Syohei YOSHIDA

;; Author: Syohei YOSHIDA <syohex@gmail.com>
;; Package-Requires: ((emacs "24.3") (direx "0"))

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

;; direx version of dired-k

;;; Code:

(require 'dired-k)
(require 'direx-project)

(defface direx-k-modified
  '((t (:foreground "orange" :weight bold)))
  "Face of added file in git repository")

(defface direx-k-untracked
  '((t (:foreground "green")))
  "Face of untracked file in git repository")

(defface direx-k-ignored
  '((t (:foreground "grey")))
  "Face of ignored file in git repository")

(defsubst direx-k--git-status-color (stat)
  (cl-case stat
    ((modified added) 'direx-k-modified)
    (untracked 'direx-k-untracked)
    (ignored 'direx-k-ignored)))

(defun direx-k--highlight-item (file stats)
  (let ((stat (gethash file stats 'normal)))
    (unless (and (file-directory-p file) (eq stat 'normal))
      (let ((ov (make-overlay (point) (line-end-position)))
            (stat-face (direx-k--git-status-color stat)))
        (when stat-face
          (overlay-put ov 'face stat-face)
          (overlay-put ov 'direx-k t))))))

(defun direx-k--remove-overlays ()
  (dolist (ov (overlays-in (point-min) (point-max)))
    (when (overlay-get ov 'direx-k)
      (delete-overlay ov))))

(defun direx-k--highlight-git-information (stats buf)
  (with-current-buffer buf
    (direx-k--remove-overlays)
    (save-excursion
      (goto-char (point-min))
      (let ((continue t))
        (while (and continue (not (eobp)))
          (direx:awhen (direx:item-at-point)
            (let ((file (direx:item-tree it)))
              (direx:awhen (direx:file-full-name file)
                (direx-k--highlight-item it stats))))
          (setq continue (ignore-errors (direx:next-item) t)))))))

(defsubst direx-k--process-buffer ()
  (get-buffer-create (format "*direx-k-%s*" dired-directory)))

;;;###autoload
(defun direx-k ()
  (interactive)
  (unless (eq major-mode 'direx:direx-mode)
    (error "This buffer is not `direx'"))
  (unless (direx-project:vc-root-p default-directory)
    (error "Here is not version control root"))
  (dired-k--start-git-status
   '("git" "status" "--porcelain" "--untracked-files=normal" ".")
   default-directory (direx-k--process-buffer)
   'direx-k--highlight-git-information))

(provide 'direx-k)

;;; direx-k.el ends here
