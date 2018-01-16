;;; magithub-edit-mode.el --- message-editing mode   -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: multimedia

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

;; Edit generic Github (markdown) content.  To be used for comments,
;; issues, pull requests, etc.

;;; Code:

(require 'markdown-mode)
(require 'git-commit)

(defvar magithub-edit-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "C-c C-c") #'magithub-edit-submit)
    (define-key m (kbd "C-c C-k") #'magithub-edit-cancel)
    m))

;;;###autoload
(define-derived-mode magithub-edit-mode gfm-mode "Magithub-Edit"
  "Major mode for editing Github issues and pull requests.")

(defvar-local magithub-edit-submit-function nil)
(defvar-local magithub-edit-cancel-function nil)
(defvar-local magithub-edit-previous-buffer nil)

(defface magithub-edit-title
  '((t :inherit markdown-header-face-1))
  "Face used for the title in issues and pull requests."
  :group 'magithub-faces)

(defun magithub-edit-submit ()
  (interactive)
  (magithub-edit--done magithub-edit-submit-function)
  (magithub-cache-without-cache t
    (magit-refresh-buffer)))
(defun magithub-edit-cancel ()
  (interactive)
  (magithub-edit--done magithub-edit-cancel-function))
(defun magithub-edit--done (callback)
  (let ((prevbuf magithub-edit-previous-buffer))
    (save-excursion
      (when-let ((newbuf (call-interactively callback)))
        (when (bufferp newbuf)
          (switch-to-buffer newbuf))))
    (kill-buffer)
    (when prevbuf
      (let ((switch-to-buffer-preserve-window-point t))
        (switch-to-buffer prevbuf)))))
(defun magithub-edit-new (buffer-name submit-func cancel-func local-map setup)
  (declare (indent 4))
  (let ((prevbuf (current-buffer)))
    (with-current-buffer (get-buffer-create buffer-name)
      (magithub-edit-mode)
      (use-local-map (let ((m local-map))
                       (set-keymap-parent m magithub-edit-mode-map)
                       m))
      (funcall setup)
      (setq magithub-edit-previous-buffer prevbuf
            magithub-edit-submit-function submit-func
            magithub-edit-cancel-function cancel-func)
      (switch-to-buffer-other-window (current-buffer)))))

(provide 'magithub-edit-mode)
;;; magithub-edit-mode.el ends here
