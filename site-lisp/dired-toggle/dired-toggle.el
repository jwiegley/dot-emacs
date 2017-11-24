;;; dired-toggle.el --- provide a simple way to toggle dired buffer for current directory
;;
;; Copyright (C) 2013, Xu FaSheng
;;
;; Author: Xu FaSheng <fasheng.xu@gmail.com>
;; Maintainer: Xu FaSheng
;; Version: 0.1
;; URL: https://github.com/fasheng/dired-toggle
;; Keywords: dired, toggle
;; Compatibility: GNU Emacs: 24.x
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;; Description:
;;
;; `dired-toggle' provide an simple way to toggle dired buffer for
;; current directory(similar to `dired-jump'), and the target buffer
;; is specified so that it will be divided from other dired buffers,
;; for example the dired buffer only shown in a special name which
;; could be edit through the variable `dired-toggle-buffer-name', and
;; it will include a minor mode named `dired-toggle-mode' to ensure
;; all the actions(such as change directory and open a selected file)
;; under the dired buffer will not influence other dired buffers and
;; works as we expected.
;;
;; You could custom the toggled window's size and side through
;; variable `dired-toggle-window-size' and `dired-toggle-window-side'.
;;
;; Source: https://github.com/fasheng/dired-toggle
;;
;; Tips: For a good user experience you may want to use
;; `dired-details.el' or `dired-hide-details-mode' if use Emacs 24.4
;; or later.
;;
;;
;; Usage:
;;
;; Just add the following to your .emacs:
;;
;; (global-set-key (kbd "<f5>") 'dired-toggle)
;;
;; You could also custom functions after `dired-toggle-mode' enabled,
;; for example enable `visual-line-mode' for our narrow dired buffer:
;;
;; (add-hook 'dired-toggle-mode-hook
;;           (lambda () (interactive)
;;             (visual-line-mode 1)
;;             (setq-local visual-line-fringe-indicators '(nil right-curly-arrow))
;;             (setq-local word-wrap nil)))
;;
;;
;; Default key-bindings:
;;
;; | "q"       | dired-toggle-action-quit         |
;; | "RET"     | dired-toggle-action-find-file    |
;; | "^"       | dired-toggle-action-up-directory |
;; | "C-c C-u" | dired-toggle-action-up-directory |
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(require 'dired)

(defvar dired-toggle-buffer-name "*Dired Toggle*"
  "Target buffer name for `dired-toggle'.")

(defvar dired-toggle-window-size 24
  "Target window size for `dired-toggle'.")

(defvar dired-toggle-window-side 'left
  "Target window's place side for `dired-toggle', could be 'left, 'right,
'below or 'above, more information to see `split-window'.")

(defvar dired-toggle-modeline-lighter " DiredTog"
  "Modeline lighter for `dired-toggle-mode'.")

(defvar-local dired-toggle-refwin nil
  "Mark the referred window that jumping from.")

(defvar dired-toggle-dired-mode-name 'dired-mode
  "Setup the default dired mode working with `dired-toggle-mode'.")

(defun dired-toggle-list-dir (buffer dir &optional mode)
  "List target directory in a buffer."
  (let ((mode (or mode dired-toggle-dired-mode-name)))
    (with-current-buffer buffer
      (setq default-directory dir)
      (if (eq mode major-mode)
          (setq dired-directory dir)
        (funcall mode dir))
      (dired-toggle-mode 1)
      ;; default-directory and dired-actual-switches are set now
      ;; (buffer-local), so we can call dired-readin:
      (unwind-protect
          (progn (dired-readin)))
      )))

(defun dired-toggle-action-quit ()
  "Custom quit action under `dired-toggle-mode'."
  (interactive)
  (if (one-window-p)
      (quit-window)
    (delete-window)))

(defun dired-toggle-action-find-file ()
  "Custom item action under `dired-toggle-mode'."
  (interactive)
  (let* ((buffer (current-buffer))
         (file (dired-get-file-for-visit))
         (dir-p (file-directory-p file)))
    (if dir-p                           ;open a directory
        (dired-toggle-list-dir buffer (file-name-as-directory file))
      ;; open a file, and delete the referred window firstly
      (if (and (window-live-p dired-toggle-refwin)
               (not (window-minibuffer-p dired-toggle-refwin))
               ;; Some times `dired-toggle-refwin' maybe dired-toggle
               ;; window itself, so just ignore it.
               (not (equal (selected-window) dired-toggle-refwin)))
          (delete-window dired-toggle-refwin))
      (dired-find-alternate-file)
    )))

(defun dired-toggle-action-up-directory ()
  "Custom up directory action under `dired-toggle-mode'."
  (interactive)
  (let* ((buffer (current-buffer))
         (dir (dired-current-directory))
         (up (file-name-directory (directory-file-name dir))))
    (or (dired-goto-file (directory-file-name dir))
        ;; Only try dired-goto-subdir if buffer has more than one dir.
        (and (cdr dired-subdir-alist)
             (dired-goto-subdir up))
        (progn
          (dired-toggle-list-dir buffer up)
          (dired-goto-file dir)))))

(defvar dired-toggle-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "q" 'dired-toggle-action-quit)
    (define-key map (kbd "RET") 'dired-toggle-action-find-file)
    (define-key map "^" 'dired-toggle-action-up-directory)
    (define-key map "\C-c\C-u" 'dired-toggle-action-up-directory)
    map)
  "Keymap for `dired-toggle-mode'.")

(defvar dired-toggle-mode-hook nil
  "Function(s) to call after `dired-toggle-mode' enabled.")

(define-minor-mode dired-toggle-mode
  "Assistant minor mode for `dired-toggle'."
  :lighter dired-toggle-modeline-lighter
  :keymap dired-toggle-mode-map
  :after-hook dired-toggle-mode-hook
  )

;;;###autoload
(defun dired-toggle (&optional dir)
  "Toggle current buffer's directory."
  (interactive)
  (let* ((win (selected-window))
         (buf (buffer-name))
         (file (buffer-file-name))
         (dir (or dir (if file (file-name-directory file) default-directory)))
         (size dired-toggle-window-size)
         (side dired-toggle-window-side)
         (target-bufname dired-toggle-buffer-name)
         (target-buf (get-buffer-create target-bufname))
         (target-window (get-buffer-window target-buf))
         (dired-buffer-with-same-dir (dired-find-buffer-nocreate dir))
         (new-dired-buffer-p
          (or (not dired-buffer-with-same-dir)
              (not (string= target-bufname
                            (buffer-name dired-buffer-with-same-dir))))))
    (if target-window            ;hide window if target buffer is shown
        (if (one-window-p)
            (quit-window)
          (delete-window target-window))
      ;; Else show target buffer in a side window
      (progn
        (setq target-window (split-window win (- size) side))
        (select-window target-window)
        (switch-to-buffer target-buf)
        ;; init dired-mode
        (if new-dired-buffer-p
            (dired-toggle-list-dir target-buf dir))
        (with-current-buffer target-buf
          ;; TODO mark the referred window that jumping from
          (setq-local dired-toggle-refwin win)
          ;; try to select target file
          (if file
              (or (dired-goto-file file)
                  ;; Toggle omitting, if it is on, and try again.
                  (when dired-omit-mode
                    (dired-omit-mode 0)
                    (dired-goto-file file)))))
        ))))

(provide 'dired-toggle)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; dired-toggle.el ends here
